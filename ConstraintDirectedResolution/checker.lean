import main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private partial def CollapseCertConstNames (e : Lean.Expr) (acc : Array Lean.Name := #[]) :
    Array Lean.Name :=
  match e with
  | .const name _ =>
      if acc.contains name then acc else acc.push name
  | .app fn arg =>
      CollapseCertConstNames arg (CollapseCertConstNames fn acc)
  | .lam _ type body _ =>
      CollapseCertConstNames body (CollapseCertConstNames type acc)
  | .forallE _ type body _ =>
      CollapseCertConstNames body (CollapseCertConstNames type acc)
  | .letE _ type value body _ =>
      CollapseCertConstNames body
        (CollapseCertConstNames value (CollapseCertConstNames type acc))
  | .mdata _ body =>
      CollapseCertConstNames body acc
  | .proj _ _ body =>
      CollapseCertConstNames body acc
  | _ =>
      acc

private def shouldUnfoldCollapseCertConst (decl : Lean.Name) : Lean.Meta.MetaM Bool := do
  if decl.isInternalDetail then
    return false
  let some info := (← Lean.getEnv).find? decl
    | return false
  let type ← Lean.instantiateMVars info.type
  if (← Lean.Meta.isDefEq type (Lean.mkConst ``Context)) then
    return true
  if (← Lean.Meta.isDefEq type (Lean.mkConst ``EvalOpEngine)) then
    return true
  if (← Lean.Meta.isDefEq type (Lean.mkConst ``Expr)) then
    return true
  return false

private def CollapseCertUnfoldDecls (target : Lean.Expr) : Lean.Meta.MetaM (Array Lean.Name) := do
  let mut decls := #[]
  for decl in CollapseCertConstNames target do
    if (← shouldUnfoldCollapseCertConst decl) then
      decls := decls.push decl
  return decls

private partial def unfoldCollapseCertDecls (decls : Array Lean.Name) :
    Lean.Expr → Lean.Meta.MetaM Lean.Expr
  | .app fn arg => do
      let fn ← unfoldCollapseCertDecls decls fn
      let arg ← unfoldCollapseCertDecls decls arg
      let e := Lean.mkApp fn arg
      match (← Lean.Meta.delta? e (fun decl => decls.contains decl)) with
      | some e => Lean.Meta.whnf e
      | none => pure e
  | .lam name type body info => do
      let type ← unfoldCollapseCertDecls decls type
      let body ← unfoldCollapseCertDecls decls body
      pure (.lam name type body info)
  | .forallE name type body info => do
      let type ← unfoldCollapseCertDecls decls type
      let body ← unfoldCollapseCertDecls decls body
      pure (.forallE name type body info)
  | .letE name type value body nondep => do
      let type ← unfoldCollapseCertDecls decls type
      let value ← unfoldCollapseCertDecls decls value
      let body ← unfoldCollapseCertDecls decls body
      pure (.letE name type value body nondep)
  | .mdata data body => do
      let body ← unfoldCollapseCertDecls decls body
      pure (.mdata data body)
  | .proj structName idx body => do
      let body ← unfoldCollapseCertDecls decls body
      pure (.proj structName idx body)
  | e@(.const decl _) => do
      match (← Lean.Meta.delta? e (fun candidate => candidate == decl && decls.contains decl)) with
      | some e => Lean.Meta.whnf e
      | none => pure e
  | e =>
      pure e

private def CollapseCertRawFailure (target : Lean.Expr) :
    Lean.Meta.MetaM Lean.MessageData := do
  pure m!"discharge_collapse_cert failed\nfailed goal:\n{← Lean.Meta.ppExpr target}"

private def ambiguityDiagnosticCoreDecls : Array Lean.Name := #[
  ``enumerateAdmissible,
  ``enumerateRealizedArgs,
  ``enumerateRealizedArgsFrom,
  ``pickAllExact,
  ``pickAllOption,
  ``optionArgMatches,
  ``filterOps,
  ``filterNonOps,
  ``Term.isOp,
  ``Term.isNonOp,
  ``Term.typeOf,
  ``Term.typeOfList,
  ``Term.allSameTy
]

private def normalizeAmbiguityDiagnosticExpr (decls : Array Lean.Name) (e : Lean.Expr) :
    Lean.Meta.MetaM Lean.Expr := do
  let e ← unfoldCollapseCertDecls (decls ++ ambiguityDiagnosticCoreDecls) e
  Lean.Meta.withTransparency Lean.Meta.TransparencyMode.default do
    Lean.Meta.reduce e

private partial def listExprElems? (e : Lean.Expr) :
    Lean.Meta.MetaM (Option (Array Lean.Expr)) := do
  let e ← Lean.Meta.whnf e
  e.withApp fun fn args => do
  if fn.isConstOf ``List.nil && args.size == 1 then
    return some #[]
  else if fn.isConstOf ``List.cons && args.size == 3 then
    let some tail ← listExprElems? args[2]!
      | return none
    return some (#[args[1]!] ++ tail)
  else
    return none

private def ppAmbiguityExprString (e : Lean.Expr) : Lean.Meta.MetaM String := do
  return toString (← Lean.Meta.ppExpr e)

private def exprStringLit? (e : Lean.Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

private partial def diagnosticTyEq : Ty → Ty → Bool
  | Ty.nat, Ty.nat => true
  | Ty.str, Ty.str => true
  | Ty.option τ₁, Ty.option τ₂ => diagnosticTyEq τ₁ τ₂
  | Ty.seq τ₁, Ty.seq τ₂ => diagnosticTyEq τ₁ τ₂
  | Ty.tuple τs₁, Ty.tuple τs₂ => diagnosticTyListEq τs₁ τs₂
  | Ty.nominal label₁ τ₁, Ty.nominal label₂ τ₂ =>
      label₁ == label₂ && diagnosticTyEq τ₁ τ₂
  | Ty.arrow args₁ out₁, Ty.arrow args₂ out₂ =>
      diagnosticTyListEq args₁ args₂ && diagnosticTyEq out₁ out₂
  | _, _ => false
where
  diagnosticTyListEq : List Ty → List Ty → Bool
    | [], [] => true
    | τ₁ :: τs₁, τ₂ :: τs₂ =>
        diagnosticTyEq τ₁ τ₂ && diagnosticTyListEq τs₁ τs₂
    | _, _ => false

private def diagnosticAllSameTy (τ : Ty) : List Ty → Bool
  | [] => true
  | τ' :: τs => diagnosticTyEq τ τ' && diagnosticAllSameTy τ τs

private def mapMOption {α β : Type} (xs : List α) (f : α → Lean.Meta.MetaM (Option β)) :
    Lean.Meta.MetaM (Option (List β)) := do
  let mut out := []
  for x in xs do
    match (← f x) with
    | some y => out := out ++ [y]
    | none => return none
  return some out

private partial def tyExprValue? (e : Lean.Expr) :
    Lean.Meta.MetaM (Option Ty) := do
  let e ← Lean.Meta.whnf e
  e.withApp fun fn args => do
    if fn.isConstOf ``Ty.nat && args.size == 0 then
      return some Ty.nat
    else if fn.isConstOf ``Ty.str && args.size == 0 then
      return some Ty.str
    else if fn.isConstOf ``Ty.option && args.size == 1 then
      return (Ty.option <$> (← tyExprValue? args[0]!))
    else if fn.isConstOf ``Ty.seq && args.size == 1 then
      return (Ty.seq <$> (← tyExprValue? args[0]!))
    else if fn.isConstOf ``Ty.tuple && args.size == 1 then
      let some elems ← listExprElems? args[0]!
        | return none
      let some tys ← mapMOption elems.toList tyExprValue?
        | return none
      return some (Ty.tuple tys)
    else if fn.isConstOf ``Ty.nominal && args.size == 2 then
      let some label := exprStringLit? args[0]!
        | return none
      let some τ ← tyExprValue? args[1]!
        | return none
      return some (Ty.nominal label τ)
    else if fn.isConstOf ``Ty.arrow && args.size == 2 then
      let some argElems ← listExprElems? args[0]!
        | return none
      let some argTys ← mapMOption argElems.toList tyExprValue?
        | return none
      let some outTy ← tyExprValue? args[1]!
        | return none
      return some (Ty.arrow argTys outTy)
    else
      return none

private def optionTyExprValue? (e : Lean.Expr) :
    Lean.Meta.MetaM (Option (Option Ty)) := do
  let e ← Lean.Meta.whnf e
  e.withApp fun fn args => do
    if fn.isConstOf ``Option.none && args.size == 1 then
      return some none
    else if fn.isConstOf ``Option.some && args.size == 2 then
      let some τ ← tyExprValue? args[1]!
        | return none
      return some (some τ)
    else
      return none

private partial def termExprTypeOf? (e : Lean.Expr) :
    Lean.Meta.MetaM (Option Ty) := do
  let e ← Lean.Meta.whnf e
  e.withApp fun fn args => do
    if fn.isConstOf ``Term.nat && args.size == 1 then
      return some Ty.nat
    else if fn.isConstOf ``Term.str && args.size == 1 then
      return some Ty.str
    else if fn.isConstOf ``Term.none && args.size == 0 then
      return none
    else if fn.isConstOf ``Term.some && args.size == 1 then
      return (Ty.option <$> (← termExprTypeOf? args[0]!))
    else if fn.isConstOf ``Term.seqVal && args.size == 2 then
      let some headTy ← termExprTypeOf? args[0]!
        | return none
      let some tailElems ← listExprElems? args[1]!
        | return none
      let some tailTys ← mapMOption tailElems.toList termExprTypeOf?
        | return none
      if diagnosticAllSameTy headTy tailTys then
        return some (Ty.seq headTy)
      else
        return none
    else if fn.isConstOf ``Term.tupleVal && args.size == 1 then
      let some elems ← listExprElems? args[0]!
        | return none
      let some tys ← mapMOption elems.toList termExprTypeOf?
        | return none
      return some (Ty.tuple tys)
    else if fn.isConstOf ``Term.op && args.size == 1 then
      return none
    else if fn.isConstOf ``Term.wrap && args.size == 2 then
      let some label := exprStringLit? args[0]!
        | return none
      let some τ ← termExprTypeOf? args[1]!
        | return none
      return some (Ty.nominal label τ)
    else
      return none

private def termExprOpName? (e : Lean.Expr) :
    Lean.Meta.MetaM (Option String) := do
  let e ← Lean.Meta.whnf e
  e.withApp fun fn args => do
    if fn.isConstOf ``Term.op && args.size == 1 then
      return exprStringLit? args[0]!
    else
      return none

private def termExprListExpr : List Lean.Expr → Lean.Expr
  | [] => Lean.mkApp (Lean.mkConst ``List.nil [Lean.levelZero]) (Lean.mkConst ``Term)
  | t :: ts =>
      Lean.mkApp3 (Lean.mkConst ``List.cons [Lean.levelZero]) (Lean.mkConst ``Term)
        t (termExprListExpr ts)

private abbrev DiagnosticCall := Lean.Expr × Lean.Expr

private def diagnosticCallOfExprs (name : String) (args : List Lean.Expr) : DiagnosticCall :=
  (Lean.mkStrLit name, termExprListExpr args)

private partial def diagnosticPickAllExact (τ : Ty) :
    List Lean.Expr → Lean.Meta.MetaM (List (Lean.Expr × List Lean.Expr))
  | [] => pure []
  | t :: ts => do
      let restPicks ← diagnosticPickAllExact τ ts
      let restPicks := restPicks.map (fun picked => (picked.1, t :: picked.2))
      match (← termExprTypeOf? t) with
      | some τ' =>
          if diagnosticTyEq τ τ' then
            pure ((t, ts) :: restPicks)
          else
            pure restPicks
      | none =>
          pure restPicks

private partial def diagnosticPickAllOption (τ : Ty) :
    List Lean.Expr → Lean.Meta.MetaM (List (Lean.Expr × List Lean.Expr))
  | [] => pure []
  | t :: ts => do
      let restPicks ← diagnosticPickAllOption τ ts
      let restPicks := restPicks.map (fun picked => (picked.1, t :: picked.2))
      let isNone ← do
        let t' ← Lean.Meta.whnf t
        t'.withApp fun fn args =>
          pure (fn.isConstOf ``Term.none && args.size == 0)
      if isNone then
        pure ((t, ts) :: restPicks)
      else
        match (← termExprTypeOf? t) with
        | some τ' =>
            if diagnosticTyEq (Ty.option τ) τ' then
              pure ((t, ts) :: restPicks)
            else
              pure restPicks
        | none =>
            pure restPicks

private partial def diagnosticEnumerateArgs : List Ty → List Lean.Expr →
    Lean.Meta.MetaM (List (List Lean.Expr))
  | [], _bagArgs => pure [[]]
  | Ty.option τ :: expected, bagArgs => do
      let picks ← diagnosticPickAllOption τ bagArgs
      let mut present := []
      for picked in picks do
        let tails ← diagnosticEnumerateArgs expected picked.2
        present := present ++ tails.map (fun tail => picked.1 :: tail)
      if picks.isEmpty then
        let absentTails ← diagnosticEnumerateArgs expected bagArgs
        let absent := absentTails.map (fun tail => Lean.mkConst ``Term.none :: tail)
        pure (present ++ absent)
      else
        pure present
  | τ :: expected, bagArgs => do
      let picks ← diagnosticPickAllExact τ bagArgs
      let mut branches := []
      for picked in picks do
        let tails ← diagnosticEnumerateArgs expected picked.2
        branches := branches ++ tails.map (fun tail => picked.1 :: tail)
      pure branches

private partial def diagnosticEnumerateProjectiveArgs : List Ty → List Lean.Expr →
    Lean.Meta.MetaM (List (List Lean.Expr × List Lean.Expr))
  | [], bagArgs => pure [([], bagArgs)]
  | Ty.option τ :: expected, bagArgs => do
      let picks ← diagnosticPickAllOption τ bagArgs
      let mut present := []
      for picked in picks do
        let tails ← diagnosticEnumerateProjectiveArgs expected picked.2
        present := present ++ tails.map (fun result => (picked.1 :: result.1, result.2))
      if picks.isEmpty then
        let absentTails ← diagnosticEnumerateProjectiveArgs expected bagArgs
        let absent := absentTails.map (fun result => (Lean.mkConst ``Term.none :: result.1, result.2))
        pure (present ++ absent)
      else
        pure present
  | τ :: expected, bagArgs => do
      let picks ← diagnosticPickAllExact τ bagArgs
      let mut branches := []
      for picked in picks do
        let tails ← diagnosticEnumerateProjectiveArgs expected picked.2
        branches := branches ++ tails.map (fun result => (picked.1 :: result.1, result.2))
      pure branches

private def diagnosticContextLookup? (decls : Array Lean.Name)
    (Γ : Lean.Expr) (name : String) : Lean.Meta.MetaM (Option Ty) := do
  let lookup ← normalizeAmbiguityDiagnosticExpr decls (Lean.mkApp Γ (Lean.mkStrLit name))
  match (← optionTyExprValue? lookup) with
  | some ty? => pure ty?
  | none => pure none

private def diagnosticBranchesFromSyntax? (decls : Array Lean.Name)
    (Γ e : Lean.Expr) : Lean.Meta.MetaM (Option (Array DiagnosticCall)) := do
  let e ← normalizeAmbiguityDiagnosticExpr decls e
  let some elems ← listExprElems? e
    | return none
  let mut opNames := []
  let mut bagArgs := []
  for elem in elems do
    match (← termExprOpName? elem) with
    | some name => opNames := opNames ++ [name]
    | none => bagArgs := bagArgs ++ [elem]
  match opNames with
  | [name] =>
      match (← diagnosticContextLookup? decls Γ name) with
      | some (Ty.arrow [] _) => return some #[]
      | some (Ty.arrow expected _) => do
          let argLists ← diagnosticEnumerateArgs expected bagArgs
          return some (argLists.toArray.map (diagnosticCallOfExprs name))
      | _ => return some #[]
  | _ => return some #[]

private def diagnosticProjectiveBranchesFromSyntax? (decls : Array Lean.Name)
    (Γ e : Lean.Expr) :
    Lean.Meta.MetaM (Option (Array (String × List Lean.Expr × List Lean.Expr))) := do
  let e ← normalizeAmbiguityDiagnosticExpr decls e
  let some elems ← listExprElems? e
    | return none
  let mut opNames := []
  let mut bagArgs := []
  for elem in elems do
    match (← termExprOpName? elem) with
    | some name => opNames := opNames ++ [name]
    | none => bagArgs := bagArgs ++ [elem]
  match opNames with
  | [name] =>
      match (← diagnosticContextLookup? decls Γ name) with
      | some (Ty.arrow [] _) => return some #[]
      | some (Ty.arrow expected _) => do
          let argLists ← diagnosticEnumerateProjectiveArgs expected bagArgs
          return some (argLists.toArray.map (fun result => (name, result.1, result.2)))
      | _ => return some #[]
  | _ => return some #[]

private def diagnosticCallNameExpr (c : DiagnosticCall) : Lean.Expr :=
  c.1

private def diagnosticCallArgsExpr (c : DiagnosticCall) : Lean.Expr :=
  c.2

private def diagnosticCallOfRealizedExpr (rc : Lean.Expr) : DiagnosticCall :=
  (Lean.mkApp (Lean.mkConst ``RealizedCall.opName) rc,
    Lean.mkApp (Lean.mkConst ``RealizedArgs.args)
      (Lean.mkApp (Lean.mkConst ``RealizedCall.realizedArgs) rc))

private def diagnosticCallNameString (decls : Array Lean.Name) (c : DiagnosticCall) :
    Lean.Meta.MetaM String := do
  let nameExpr ← normalizeAmbiguityDiagnosticExpr decls (diagnosticCallNameExpr c)
  match exprStringLit? nameExpr with
  | some name => pure name
  | none => ppAmbiguityExprString nameExpr

private partial def termExprSummary (decls : Array Lean.Name) (e : Lean.Expr) :
    Lean.Meta.MetaM String := do
  let e ← normalizeAmbiguityDiagnosticExpr decls e
  e.withApp fun fn args => do
    if fn.isConstOf ``Term.nat && args.size == 1 then
      ppAmbiguityExprString args[0]!
    else if fn.isConstOf ``Term.str && args.size == 1 then
      ppAmbiguityExprString args[0]!
    else if fn.isConstOf ``Term.none && args.size == 0 then
      return "none"
    else if fn.isConstOf ``Term.some && args.size == 1 then
      return s!"some {← termExprSummary decls args[0]!}"
    else if fn.isConstOf ``Term.seqVal && args.size == 2 then
      let headSummary ← termExprSummary decls args[0]!
      let some tailElems ← listExprElems? args[1]!
        | return (← ppAmbiguityExprString e)
      let tailSummaries ← tailElems.mapM (termExprSummary decls)
      return s!"seq({headSummary}; [{String.intercalate ", " tailSummaries.toList}])"
    else if fn.isConstOf ``Term.tupleVal && args.size == 1 then
      let some elems ← listExprElems? args[0]!
        | return (← ppAmbiguityExprString e)
      let summaries ← elems.mapM (termExprSummary decls)
      return s!"({String.intercalate ", " summaries.toList})"
    else if fn.isConstOf ``Term.op && args.size == 1 then
      match exprStringLit? args[0]! with
      | some name => return s!"op {repr name}"
      | none => return s!"op {← ppAmbiguityExprString args[0]!}"
    else if fn.isConstOf ``Term.wrap && args.size == 2 then
      let label ←
        match exprStringLit? args[0]! with
        | some label => pure label
        | none => ppAmbiguityExprString args[0]!
      return s!"{label}({← termExprSummary decls args[1]!})"
    else
      ppAmbiguityExprString e

private def ambiguityExprSummary (decls : Array Lean.Name) (e : Lean.Expr) :
    Lean.Meta.MetaM String := do
  let e ← normalizeAmbiguityDiagnosticExpr decls e
  let some elems ← listExprElems? e
    | return (← ppAmbiguityExprString e)
  let summaries ← elems.mapM (termExprSummary decls)
  return s!"[{String.intercalate ", " summaries.toList}]"

private def diagnosticCallArgStrings (decls : Array Lean.Name) (c : DiagnosticCall) :
    Lean.Meta.MetaM (Option (Array String)) := do
  let argsExpr ← normalizeAmbiguityDiagnosticExpr decls (diagnosticCallArgsExpr c)
  let some args ← listExprElems? argsExpr
    | return none
  args.mapM (termExprSummary decls)

private def diagnosticCallSummary (decls : Array Lean.Name) (c : DiagnosticCall) :
    Lean.Meta.MetaM String := do
  let name ← diagnosticCallNameString decls c
  let some argStrings ← diagnosticCallArgStrings decls c
    | return s!"{name}(<args unavailable>)"
  return s!"{name}({String.intercalate ", " argStrings.toList})"

private partial def termExprWarningSummary (decls : Array Lean.Name) (e : Lean.Expr) :
    Lean.Meta.MetaM String := do
  let e ← normalizeAmbiguityDiagnosticExpr decls e
  e.withApp fun fn args => do
    if fn.isConstOf ``Term.nat && args.size == 1 then
      ppAmbiguityExprString args[0]!
    else if fn.isConstOf ``Term.str && args.size == 1 then
      match exprStringLit? args[0]! with
      | some s => return s!"Term.str {repr s}"
      | none => return s!"Term.str {← ppAmbiguityExprString args[0]!}"
    else if fn.isConstOf ``Term.none && args.size == 0 then
      return "none"
    else if fn.isConstOf ``Term.some && args.size == 1 then
      return s!"some {← termExprWarningSummary decls args[0]!}"
    else
      termExprSummary decls e

private def diagnosticCallWarningSummaryFromExprs
    (decls : Array Lean.Name) (name : String) (args : List Lean.Expr) :
    Lean.Meta.MetaM String := do
  let argStrings ← args.mapM (termExprWarningSummary decls)
  let args := String.intercalate " " argStrings
  if args.isEmpty then pure name else pure s!"{name} {args}"

private def unusedBranchWarningLineFromExprs
    (decls : Array Lean.Name) (branch : String × List Lean.Expr × List Lean.Expr) :
    Lean.Meta.MetaM String := do
  let selected ← diagnosticCallWarningSummaryFromExprs decls branch.1 branch.2.1
  let unused ← branch.2.2.mapM (termExprWarningSummary decls)
  return s!"{selected}, unused: {String.intercalate ", " unused}"

private def indentLines (lines : List String) : String :=
  String.intercalate "\n" (lines.map (fun line => "  " ++ line))

private def indentBlock (s : String) : String :=
  indentLines (s.splitOn "\n")

private def someTermExpr (v : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (Lean.mkConst ``Option.some [Lean.levelZero]) (Lean.mkConst ``Term) v

private partial def termValueExpr : Term → Lean.Expr
  | Term.nat n => Lean.mkApp (Lean.mkConst ``Term.nat) (Lean.mkNatLit n)
  | Term.str s => Lean.mkApp (Lean.mkConst ``Term.str) (Lean.mkStrLit s)
  | Term.none => Lean.mkConst ``Term.none
  | Term.some t => Lean.mkApp (Lean.mkConst ``Term.some) (termValueExpr t)
  | Term.seqVal head tail =>
      Lean.mkApp2 (Lean.mkConst ``Term.seqVal) (termValueExpr head)
        (termValueListExpr tail)
  | Term.tupleVal xs => Lean.mkApp (Lean.mkConst ``Term.tupleVal) (termValueListExpr xs)
  | Term.op name => Lean.mkApp (Lean.mkConst ``Term.op) (Lean.mkStrLit name)
  | Term.wrap label t =>
      Lean.mkApp2 (Lean.mkConst ``Term.wrap) (Lean.mkStrLit label) (termValueExpr t)
where
  termValueListExpr : List Term → Lean.Expr
    | [] => Lean.mkApp (Lean.mkConst ``List.nil [Lean.levelZero]) (Lean.mkConst ``Term)
    | t :: ts =>
        Lean.mkApp3 (Lean.mkConst ``List.cons [Lean.levelZero]) (Lean.mkConst ``Term)
          (termValueExpr t) (termValueListExpr ts)

private def diagnosticCallValueExpr (name : String) (args : List Term) : DiagnosticCall :=
  (Lean.mkStrLit name, termValueExpr.termValueListExpr args)

private unsafe def evalBranchValues? (enumExpr : Lean.Expr) :
    Lean.Meta.MetaM (Option (Array DiagnosticCall)) := do
  let branchTy := Lean.mkApp (Lean.mkConst ``List [Lean.levelZero]) (Lean.mkConst ``RealizedCall)
  try
    let branches ← Lean.Meta.evalExpr (List RealizedCall) branchTy enumExpr
    return some (branches.toArray.map (fun rc =>
      diagnosticCallValueExpr rc.opName rc.realizedArgs.args))
  catch _ =>
    return none

private def evalDiagnosticCallExpr (decls : Array Lean.Name)
    (evalOp : Lean.Expr) (c : DiagnosticCall) : Lean.Meta.MetaM Lean.Expr := do
  let nameExpr ← normalizeAmbiguityDiagnosticExpr decls (diagnosticCallNameExpr c)
  let argsExpr ← normalizeAmbiguityDiagnosticExpr decls (diagnosticCallArgsExpr c)
  normalizeAmbiguityDiagnosticExpr decls (Lean.mkApp2 evalOp nameExpr argsExpr)

private def CollapseCertExprDefEq (lhs rhs : Lean.Expr) :
    Lean.Meta.MetaM Bool := do
  Lean.Meta.withTransparency Lean.Meta.TransparencyMode.default do
    Lean.Meta.isDefEq lhs rhs

private def evalTargetObligationSolved (decls : Array Lean.Name)
    (evalOp v : Lean.Expr) (c : DiagnosticCall) : Lean.Elab.Tactic.TacticM Bool := do
  let evalExpr ← evalDiagnosticCallExpr decls evalOp c
  let rhs ← normalizeAmbiguityDiagnosticExpr decls (someTermExpr v)
  CollapseCertExprDefEq evalExpr rhs

private def collapseObligationSolved (decls : Array Lean.Name)
    (evalOp : Lean.Expr) (reference c : DiagnosticCall) : Lean.Elab.Tactic.TacticM Bool := do
  let lhs ← evalDiagnosticCallExpr decls evalOp c
  let rhs ← evalDiagnosticCallExpr decls evalOp reference
  CollapseCertExprDefEq lhs rhs

private def firstUnsolvedEvalTargetBranch? (decls : Array Lean.Name)
    (evalOp v : Lean.Expr) (branches : Array DiagnosticCall) :
    Lean.Elab.Tactic.TacticM (Option DiagnosticCall) := do
  for branch in branches do
    unless (← evalTargetObligationSolved decls evalOp v branch) do
      return some branch
  return none

private def firstUnsolvedCollapseBranch? (decls : Array Lean.Name)
    (evalOp : Lean.Expr) (reference : DiagnosticCall) (branches : Array DiagnosticCall) :
    Lean.Elab.Tactic.TacticM (Option DiagnosticCall) := do
  for branch in branches do
    unless (← collapseObligationSolved decls evalOp reference branch) do
      return some branch
  return none

private def firstClosedEvalMismatchBranch? (decls : Array Lean.Name)
    (evalOp v : Lean.Expr) (branches : Array DiagnosticCall) :
    Lean.Elab.Tactic.TacticM (Option DiagnosticCall) := do
  let rhs ← normalizeAmbiguityDiagnosticExpr decls (someTermExpr v)
  if rhs.hasFVar || rhs.hasExprMVar then
    return none
  let rhsSummary ← ppAmbiguityExprString rhs
  for branch in branches do
    let evalExpr ← evalDiagnosticCallExpr decls evalOp branch
    if !(evalExpr.hasFVar || evalExpr.hasExprMVar) then
      let evalSummary ← ppAmbiguityExprString evalExpr
      if evalSummary != rhsSummary then
        return some branch
  return none

private def evalTargetObligationSummary (decls : Array Lean.Name)
    (v : Lean.Expr) (branch : DiagnosticCall) : Lean.Meta.MetaM String := do
  let branchSummary ← diagnosticCallSummary decls branch
  let vSummary ← termExprSummary decls v
  return s!"evalOp {branchSummary} = some {vSummary}"

private def collapseObligationSummary (decls : Array Lean.Name)
    (reference branch : DiagnosticCall) : Lean.Meta.MetaM String := do
  let branchName ← diagnosticCallNameString decls branch
  let some branchArgs ← diagnosticCallArgStrings decls branch
    | return s!"evalOp {← diagnosticCallSummary decls branch}\n  =\nevalOp {← diagnosticCallSummary decls reference}"
  let referenceName ← diagnosticCallNameString decls reference
  let some referenceArgs ← diagnosticCallArgStrings decls reference
    | return s!"evalOp {← diagnosticCallSummary decls branch}\n  =\nevalOp {← diagnosticCallSummary decls reference}"
  return (
    s!"evalOp {repr branchName} [{String.intercalate ", " branchArgs.toList}]\n" ++
    "  =\n" ++
    s!"evalOp {repr referenceName} [{String.intercalate ", " referenceArgs.toList}]")

private def CollapseCertStructuredDiagnostics (_target : Lean.Expr)
    (decls : Array Lean.Name) (evalOp _Γ e v _enumNorm : Lean.Expr)
    (branches : Array DiagnosticCall) : Lean.Elab.Tactic.TacticM Lean.MessageData := do
  let eSummary ← ambiguityExprSummary decls e
  if branches.isEmpty then
    return Lean.stringToMessageData <|
      "Could not collapse ambiguity.\n\n" ++
      "Expression:\n" ++
      "  " ++ eSummary ++ "\n\n" ++
      "Admissible branches:\n" ++
      "  <none>\n\n" ++
      "No admissible branch could be constructed."
  let branchSummaries ← branches.mapM fun branch => diagnosticCallSummary decls branch
  let reference := branches[0]!
  let unresolvedEval? ← firstUnsolvedEvalTargetBranch? decls evalOp v branches
  let unresolvedCollapse? ← firstUnsolvedCollapseBranch? decls evalOp reference branches
  let (unresolved, obligation) ←
    match unresolvedEval?, unresolvedCollapse? with
    | _, some unresolvedCollapse => do
        let obligation ← collapseObligationSummary decls reference unresolvedCollapse
        pure (unresolvedCollapse, obligation)
    | some unresolvedEval, none => do
        let obligation ← evalTargetObligationSummary decls v unresolvedEval
        pure (unresolvedEval, obligation)
    | none, none => do
        let obligation ← ppAmbiguityExprString _enumNorm
        pure (reference, s!"no branch-local failed obligation was isolated; normalized branches: {obligation}")
  let unresolvedSummary ← diagnosticCallSummary decls unresolved
  return Lean.stringToMessageData <|
    "Could not collapse ambiguity.\n\n" ++
    "Expression:\n" ++
    "  " ++ eSummary ++ "\n\n" ++
    "Admissible branches:\n" ++
    indentLines branchSummaries.toList ++ "\n\n" ++
    "Unresolved branch:\n" ++
    "  " ++ unresolvedSummary ++ "\n\n" ++
    "Failed proof obligation:\n" ++
    indentBlock obligation ++ "\n\n" ++
    "No ambiguity-collapse certificate could be constructed."

private unsafe def CollapseCertDiagnostics (target : Lean.Expr) :
    Lean.Elab.Tactic.TacticM Lean.MessageData := do
  let raw ← CollapseCertRawFailure target
  let decls ← CollapseCertUnfoldDecls target
  let target' ← unfoldCollapseCertDecls decls target
  let target' ← Lean.Meta.whnf target'
  target'.withApp fun fn args => do
    unless fn.isConstOf ``CollapseCert && args.size == 4 do
      return raw
    let evalOp := args[0]!
    let Γ := args[1]!
    let e := args[2]!
    let v := args[3]!
    let enumExpr := Lean.mkApp2 (Lean.mkConst ``enumerateAdmissible) Γ e
    let enumNorm ← normalizeAmbiguityDiagnosticExpr decls enumExpr
    let branches ←
      match (← listExprElems? enumNorm) with
      | some branches => pure (branches.map diagnosticCallOfRealizedExpr)
      | none =>
          match (← evalBranchValues? enumNorm) with
          | some branches => pure branches
          | none =>
              match (← diagnosticBranchesFromSyntax? decls Γ e) with
              | some branches => pure branches
              | none => return raw
    CollapseCertStructuredDiagnostics target decls evalOp Γ e v enumNorm branches

private unsafe def CollapseCertClosedEvalFailure? (target : Lean.Expr) :
    Lean.Elab.Tactic.TacticM (Option Lean.MessageData) := do
  let decls ← CollapseCertUnfoldDecls target
  let target' ← unfoldCollapseCertDecls decls target
  let target' ← Lean.Meta.whnf target'
  target'.withApp fun fn args => do
    unless fn.isConstOf ``CollapseCert && args.size == 4 do
      return none
    let evalOp := args[0]!
    let Γ := args[1]!
    let e := args[2]!
    let v := args[3]!
    let enumExpr := Lean.mkApp2 (Lean.mkConst ``enumerateAdmissible) Γ e
    let enumNorm ← normalizeAmbiguityDiagnosticExpr decls enumExpr
    let branches ←
      match (← listExprElems? enumNorm) with
      | some branches => pure (branches.map diagnosticCallOfRealizedExpr)
      | none =>
          match (← evalBranchValues? enumNorm) with
          | some branches => pure branches
          | none =>
              match (← diagnosticBranchesFromSyntax? decls Γ e) with
              | some branches => pure branches
              | none => return none
    if branches.isEmpty then
      return some (← CollapseCertStructuredDiagnostics target decls evalOp Γ e v enumNorm branches)
    let some _branch ← firstClosedEvalMismatchBranch? decls evalOp v branches
      | return none
    return some (← CollapseCertStructuredDiagnostics target decls evalOp Γ e v enumNorm branches)

private unsafe def warnProjectiveUnusedIfAny (target : Lean.Expr) :
    Lean.Elab.Tactic.TacticM Unit := do
  let decls ← CollapseCertUnfoldDecls target
  let target' ← unfoldCollapseCertDecls decls target
  let target' ← Lean.Meta.whnf target'
  target'.withApp fun fn args => do
    unless fn.isConstOf ``CollapseCert && args.size == 4 do
      return ()
    let Γ := args[1]!
    let e := args[2]!
    let some branches ← diagnosticProjectiveBranchesFromSyntax? decls Γ e
      | return ()
    let withUnused := branches.toList.filter (fun branch =>
      match branch.2.2 with
      | [] => false
      | _ :: _ => true)
    match withUnused with
    | [] => return ()
    | [branch] => do
        let unused ← branch.2.2.mapM fun term =>
          termExprWarningSummary decls term
        let selected ← diagnosticCallWarningSummaryFromExprs decls branch.1 branch.2.1
        Lean.logWarning <|
          "projective admissibility ignored unused argument:\n" ++
          indentLines unused ++ "\n" ++
          "selected branch:\n" ++
          "  " ++ selected
    | branches => do
        let lines ← branches.mapM fun branch =>
          unusedBranchWarningLineFromExprs decls branch
        Lean.logWarning <|
          "warning: projective admissibility produced multiple branches with unused arguments:\n" ++
          indentLines lines

elab "normalize_collapse_cert_goal" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let target ← mvarId.getType
  let target ← Lean.instantiateMVars target
  let decls ← CollapseCertUnfoldDecls target
  let target' ← unfoldCollapseCertDecls decls target
  let target' ← Lean.Meta.whnf target'
  let target' ← Lean.Meta.withTransparency Lean.Meta.TransparencyMode.default do
    Lean.Meta.reduce target'
  if target' == target then
    pure ()
  else
    let mvarId' ← mvarId.change target'
    Lean.Elab.Tactic.replaceMainGoal [mvarId']

/-- Certificate-discharge tactic for local hypotheses and small finite
enumerations. It tries local certificates/collapses first, then semantic
singleton, invariant collapse, and finite branch enumeration. Branch goals use
generic finite-enumerator normalization, `rfl`, `simp`, `grind`, and arithmetic
solvers. -/
unsafe def dischargeCollapseCertTactic : Lean.Elab.Tactic.TacticM Unit := do
  let target ← Lean.Elab.Tactic.getMainTarget
  if let some msg ← CollapseCertClosedEvalFailure? target then
    throwError msg
  let savedGoals ← Lean.Elab.Tactic.getGoals
  let savedMessages ← Lean.Core.getMessageLog
  let script ← `(tactic|
    solve
    | assumption
    | apply finite_branch_collapse_cert <;> assumption
    | apply finite_enumeration_collapse_cert
      · normalize_collapse_cert_goal
        simp [enumerateAdmissible, pickAllExact, pickAllOption, optionArgMatches,
          enumerateRealizedArgs, enumerateRealizedArgsFrom,
          filterOps, filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf,
          Term.typeOfList, Term.allSameTy]
      · normalize_collapse_cert_goal
        intro c h_mem
        simp_all [enumerateAdmissible, realizedEvalName,
          realizedEvalArgs, enumerateRealizedArgs, enumerateRealizedArgsFrom,
          pickAllExact, pickAllOption, optionArgMatches, filterOps, filterNonOps,
          Term.isOp, Term.isNonOp, Term.typeOf, Term.typeOfList, Term.allSameTy,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        <;> first
          | normalize_collapse_cert_goal
            simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          | normalize_collapse_cert_goal
            rfl
          | rfl
          | native_decide
          | simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          | grind
          | omega
          | nlinarith
          | norm_num
    | apply CollapseCert.unique
      · rw [unique_admissible_iff_dedup_singleton]
        normalize_collapse_cert_goal
        simp [enumerateAdmissible, pickAllExact, pickAllOption, optionArgMatches,
          enumerateRealizedArgs, enumerateRealizedArgsFrom,
          filterOps, filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf,
          Term.typeOfList, Term.allSameTy]
      · first
        | normalize_collapse_cert_goal
          rfl
        | rfl
        | native_decide
        | simp_all [enumerateAdmissible,
            enumerateRealizedArgs, enumerateRealizedArgsFrom, realizedEvalName,
            realizedEvalArgs, pickAllExact, pickAllOption, optionArgMatches, filterOps, filterNonOps,
            Term.isOp, Term.isNonOp, Term.typeOf, Term.typeOfList, Term.allSameTy,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        | grind
        | omega
        | nlinarith
        | norm_num
    | apply CollapseCert.invariantCollapse
      · first
        | rfl
        | normalize_collapse_cert_goal
          simp_all [realizedEvalName, enumerateAdmissible, enumerateRealizedArgs,
            enumerateRealizedArgsFrom,
            filterOps, filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf,
            Term.typeOfList, Term.allSameTy]
      · assumption
      · assumption)
  let solved ← Lean.Elab.Tactic.withSuppressedMessages do
    try
      Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic script
      pure true
    catch _ =>
      pure false
  let remaining ← Lean.Elab.Tactic.getGoals
  unless solved && remaining.isEmpty do
    Lean.Elab.Tactic.setGoals savedGoals
    Lean.Core.setMessageLog savedMessages
    throwError (← CollapseCertDiagnostics target)
  warnProjectiveUnusedIfAny target

unsafe def dischargeCollapseCertProof (target : Lean.Expr) :
    Lean.Elab.Term.TermElabM (Except Lean.MessageData Lean.Expr) := do
  let proof ← Lean.Meta.mkFreshExprMVar target
  try
    let goals ← Lean.Elab.Tactic.run proof.mvarId! dischargeCollapseCertTactic
    if goals.isEmpty then
      return Except.ok (← Lean.instantiateMVars proof)
    else
      return Except.error m!"discharge_collapse_cert left unsolved goals"
  catch ex =>
    return Except.error (ex.toMessageData)

elab "discharge_collapse_cert" : tactic => unsafe do
  dischargeCollapseCertTactic
