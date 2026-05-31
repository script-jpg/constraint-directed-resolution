import main
import checker
import Lean.Elab.Term
import Lean.Elab.Command
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.List.Basic

/- A program term is either a plain term or a back-index to a previous index in the list of ProgramExprs, ProgramIndex -/
inductive ProgramTerm where
  | term : Term → ProgramTerm
  | index : Nat → ProgramTerm
  | some : ProgramTerm → ProgramTerm
  | none : ProgramTerm
  | seq : ProgramTerm → List ProgramTerm → ProgramTerm
  | tuple : List ProgramTerm → ProgramTerm
  | wrap : String → ProgramTerm → ProgramTerm

/- A ProgramExpr is a list of program terms -/
abbrev ProgramExpr := List ProgramTerm

abbrev Program := List ProgramExpr

/- Helper to check if a single expression only references strictly smaller indices -/
def ProgramTerm.wellFormedAt (idx : Nat) : ProgramTerm → Prop
  | ProgramTerm.term _ => True
  | ProgramTerm.index n => n < idx
  | ProgramTerm.some t => ProgramTerm.wellFormedAt idx t
  | ProgramTerm.none => True
  | ProgramTerm.seq head tail =>
      ProgramTerm.wellFormedAt idx head ∧
        ∀ t ∈ tail, ProgramTerm.wellFormedAt idx t
  | ProgramTerm.tuple ts => ∀ t ∈ ts, ProgramTerm.wellFormedAt idx t
  | ProgramTerm.wrap _ t => ProgramTerm.wellFormedAt idx t

def ProgramExpr.wellFormedAt (idx : Nat) (pExpr : ProgramExpr) : Prop :=
  ∀ pt ∈ pExpr, pt.wellFormedAt idx

/- A program is well-formed if every expression at position `i` only
   references indices `< i` -/
def Program.WellFormed (p : Program) : Prop :=
  ∀ i : Fin p.length, ProgramExpr.wellFormedAt (i : ℕ) (p.get i)

def ProgramTerm.resolve (acc : List Term) : ProgramTerm → Option Term
  | ProgramTerm.term t  => Option.some t
  | ProgramTerm.index i => acc[i]?
  | ProgramTerm.some t => do
      let t ← ProgramTerm.resolve acc t
      Option.some (Term.some t)
  | ProgramTerm.none => Option.some Term.none
  | ProgramTerm.seq head tail => do
      let head ← ProgramTerm.resolve acc head
      let tail ← tail.mapM (ProgramTerm.resolve acc)
      Option.some (Term.seqVal head tail)
  | ProgramTerm.tuple ts => do
      let ts ← ts.mapM (ProgramTerm.resolve acc)
      Option.some (Term.tupleVal ts)
  | ProgramTerm.wrap label t => do
      let t ← ProgramTerm.resolve acc t
      Option.some (Term.wrap label t)

def ProgramExpr.resolve (acc : List Term) (e : ProgramExpr) : Option Expr :=
  e.mapM (ProgramTerm.resolve acc)

namespace Program

structure EvalError where
  idx : Nat
  resolved? : Option Expr
  resolveError? : Option String := none
  proofError? : Option String := none
deriving Repr

abbrev StepProof (evalOp : EvalOpEngine) (Γ : Context) (e : Expr) :=
  { v : Term // CollapseCert evalOp Γ e v }

abbrev ManualProofProvider (evalOp : EvalOpEngine) (Γ : Context) :=
  (idx : Nat) → (e : Expr) → Option (StepProof evalOp Γ e)

def noManualProofs (evalOp : EvalOpEngine) (Γ : Context) :
    ManualProofProvider evalOp Γ :=
  fun _ _ => none

def manualProofsOfList {evalOp : EvalOpEngine} {Γ : Context}
    (entries : List (Nat × ((e : Expr) → Option (StepProof evalOp Γ e)))) :
    ManualProofProvider evalOp Γ :=
  fun idx e =>
    match entries.find? (fun entry => entry.1 == idx) with
    | some entry => entry.2 e
    | none => none

private partial def termExpr : Term → Lean.Expr
  | Term.nat n => Lean.mkApp (Lean.mkConst ``Term.nat) (Lean.mkNatLit n)
  | Term.str s => Lean.mkApp (Lean.mkConst ``Term.str) (Lean.mkStrLit s)
  | Term.none => Lean.mkConst ``Term.none
  | Term.some t => Lean.mkApp (Lean.mkConst ``Term.some) (termExpr t)
  | Term.seqVal head tail =>
      Lean.mkApp2 (Lean.mkConst ``Term.seqVal) (termExpr head) (termListExpr tail)
  | Term.tupleVal xs => Lean.mkApp (Lean.mkConst ``Term.tupleVal) (termListExpr xs)
  | Term.op name => Lean.mkApp (Lean.mkConst ``Term.op) (Lean.mkStrLit name)
  | Term.wrap label t =>
      Lean.mkApp2 (Lean.mkConst ``Term.wrap) (Lean.mkStrLit label) (termExpr t)
where
  termListExpr : List Term → Lean.Expr
    | [] => Lean.mkApp (Lean.mkConst ``List.nil [Lean.levelZero]) (Lean.mkConst ``Term)
    | t :: ts =>
        Lean.mkApp3 (Lean.mkConst ``List.cons [Lean.levelZero]) (Lean.mkConst ``Term)
          (termExpr t) (termListExpr ts)

private def exprExpr (e : Expr) : Lean.Expr :=
  termExpr.termListExpr e

private def collapseCertTarget
    (evalOpExpr ΓExpr : Lean.Expr) (e : Expr) (v : Term) : Lean.Expr :=
  Lean.mkApp4 (Lean.mkConst ``CollapseCert) evalOpExpr ΓExpr (exprExpr e) (termExpr v)

private unsafe def autoStep?
    (evalOp : EvalOpEngine) (Γ : Context)
    (evalOpExpr ΓExpr : Lean.Expr) (e : Expr) :
    Lean.Elab.Term.TermElabM (Except String (Option Term)) := do
  let mut lastError? : Option String := none
  for v in _root_.candidateValues evalOp Γ e do
    let target := collapseCertTarget evalOpExpr ΓExpr e v
    match (← dischargeCollapseCertProof target) with
    | Except.ok _proof =>
        return Except.ok (some v)
    | Except.error msg =>
        lastError? := some (← msg.toString)
  match lastError? with
  | some msg => return Except.error msg
  | none => return Except.ok none

private def resolveError (idx : Nat) : EvalError where
  idx := idx
  resolved? := none
  resolveError? := some s!"failed to resolve program expression at index {idx}"

private def proofError (idx : Nat) (e : Expr) (msg : String) : EvalError where
  idx := idx
  resolved? := some e
  proofError? := some msg

unsafe def eval
    (evalOp : EvalOpEngine)
    (Γ : Context)
    (evalOpExpr ΓExpr : Lean.Expr)
    (p : Program)
    (manual : ManualProofProvider evalOp Γ := noManualProofs evalOp Γ)
    (acc : List Term := [])
    (idx : Nat := 0) :
    Lean.Elab.Term.TermElabM (Except EvalError (List Term)) := do
  if hidx : idx < p.length then
    let pExpr := p.get ⟨idx, hidx⟩
    match ProgramExpr.resolve acc pExpr with
    | none =>
        return Except.error (resolveError idx)
    | some e =>
        match (← autoStep? evalOp Γ evalOpExpr ΓExpr e) with
        | Except.ok (some v) =>
            eval evalOp Γ evalOpExpr ΓExpr p manual (acc ++ [v]) (idx + 1)
        | Except.ok none =>
            match manual idx e with
            | some step =>
                eval evalOp Γ evalOpExpr ΓExpr p manual (acc ++ [step.1]) (idx + 1)
            | none =>
                return Except.error
                  (proofError idx e "no candidate values were produced by evalOp")
        | Except.error autoMsg =>
            match manual idx e with
            | some step =>
                eval evalOp Γ evalOpExpr ΓExpr p manual (acc ++ [step.1]) (idx + 1)
            | none =>
                return Except.error (proofError idx e autoMsg)
  else
    return Except.ok acc

unsafe def eval?
    (evalOp : EvalOpEngine)
    (Γ : Context)
    (evalOpExpr ΓExpr : Lean.Expr)
    (p : Program)
    (manual : ManualProofProvider evalOp Γ := noManualProofs evalOp Γ)
    (acc : List Term := [])
    (idx : Nat := 0) :
    Lean.Elab.Term.TermElabM (Option (List Term)) := do
  match (← eval evalOp Γ evalOpExpr ΓExpr p manual acc idx) with
  | Except.ok terms => return some terms
  | Except.error _ => return none

end Program

namespace ProgramDsl

open Lean Elab Command Parser

declare_syntax_cat program_ty
syntax:max "nat" : program_ty
syntax:max "str" : program_ty
syntax:max "option " program_ty:max : program_ty
syntax:max "seq " program_ty:max : program_ty
syntax:max "(" program_ty,* ")" : program_ty
syntax:max ident ":" program_ty:max : program_ty
syntax:50 program_ty:51 " -> " program_ty:50 : program_ty
syntax:50 program_ty:51 " → " program_ty:50 : program_ty

declare_syntax_cat program_context_decl
syntax ident " : " program_ty : program_context_decl

declare_syntax_cat program_atom
syntax "seq" "(" program_atom,* ")" : program_atom
syntax "wrap" "(" strLit "," program_atom ")" : program_atom
syntax "wrap" "(" ident "," program_atom ")" : program_atom
syntax ident "(" program_atom,* ")" : program_atom
syntax ident : program_atom
syntax num : program_atom
syntax strLit : program_atom
syntax "@" num : program_atom
syntax "{" term "}" : program_atom

declare_syntax_cat program_step
syntax "[" program_atom,+ "]" : program_step

declare_syntax_cat program_manual_alt
syntax "|" num " => " term : program_manual_alt

syntax (name := programModuleCmd)
  "program_module " ident " where" ppLine
  "context" ppLine
  program_context_decl*
  "engine" ppLine
  term ppLine
  "program" ppLine
  program_step*
  ("manual_proofs" ppLine program_manual_alt*)?
  "end" : command

syntax (name := runProgramCmd) "#run_program" : command

structure ProgramModuleInfo where
  mainModule : Name
  userName : Name
  contextName : Name
  evalName : Name
  programName : Name
  manualName? : Option Name
deriving Inhabited, Repr

initialize programModuleExt :
    SimplePersistentEnvExtension ProgramModuleInfo (Array ProgramModuleInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun xs x => xs.push x
    addImportedFn := fun imported => imported.foldl (init := #[]) (· ++ ·)
  }

private def numLit! : Syntax → CommandElabM Nat
  | stx =>
      match stx.isNatLit? with
      | some n => pure n
      | none => throwErrorAt stx "expected numeral"

private partial def tySyntax : Syntax → CommandElabM (TSyntax `term)
  | `(program_ty| nat) => `(Ty.nat)
  | `(program_ty| str) => `(Ty.str)
  | `(program_ty| option $τ:program_ty) => do
      let τ ← tySyntax τ
      `(Ty.option $τ)
  | `(program_ty| seq $τ:program_ty) => do
      let τ ← tySyntax τ
      `(Ty.seq $τ)
  | `(program_ty| ($τs:program_ty,*)) => do
      let elems ← τs.getElems.mapM tySyntax
      `(Ty.tuple [$elems,*])
  | `(program_ty| $label:ident : $τ:program_ty) => do
      let τ ← tySyntax τ
      `(Ty.nominal $(Syntax.mkStrLit label.getId.getString!) $τ)
  | `(program_ty| $arg:program_ty -> $out:program_ty) => arrowSyntax arg out
  | `(program_ty| $arg:program_ty → $out:program_ty) => arrowSyntax arg out
  | stx => throwErrorAt stx "unsupported type syntax"
where
  arrowParts (stx : Syntax) : CommandElabM (Array (TSyntax `term) × TSyntax `term) := do
    match stx with
    | `(program_ty| $arg:program_ty -> $out:program_ty) => do
        let arg ← tySyntax arg
        let (args, out) ← arrowParts out
        pure (#[arg] ++ args, out)
    | `(program_ty| $arg:program_ty → $out:program_ty) => do
        let arg ← tySyntax arg
        let (args, out) ← arrowParts out
        pure (#[arg] ++ args, out)
    | other => pure (#[], ← tySyntax other)
  arrowSyntax (arg out : Syntax) : CommandElabM (TSyntax `term) := do
    let arg ← tySyntax arg
    let (args, out) ← arrowParts out
    let args := #[arg] ++ args
    `(Ty.arrow [$args,*] $out)

private partial def termSyntaxOfTerm : _root_.Term → CommandElabM (TSyntax `term)
  | .nat n => `(Term.nat $(Syntax.mkNumLit (toString n)))
  | .str s => `(Term.str $(Syntax.mkStrLit s))
  | .none => `(Term.none)
  | .some t => do
      let t ← termSyntaxOfTerm t
      `(Term.some $t)
  | .seqVal head tail => do
      let head ← termSyntaxOfTerm head
      let tail ← tail.mapM termSyntaxOfTerm
      let tail := tail.toArray
      `(Term.seqVal $head [$tail,*])
  | .tupleVal xs => do
      let xs ← xs.mapM termSyntaxOfTerm
      let xs := xs.toArray
      `(Term.tupleVal [$xs,*])
  | .op name => `(Term.op $(Syntax.mkStrLit name))
  | .wrap label t => do
      let t ← termSyntaxOfTerm t
      `(Term.wrap $(Syntax.mkStrLit label) $t)

private def programTermSyntaxOfTerm (t : _root_.Term) : CommandElabM (TSyntax `term) := do
  let t ← termSyntaxOfTerm t
  `(ProgramTerm.term $t)

private partial def programTermSyntaxOfProgramTerm : ProgramTerm → CommandElabM (TSyntax `term)
  | .term t => programTermSyntaxOfTerm t
  | .index n => `(ProgramTerm.index $(Syntax.mkNumLit (toString n)))
  | .some t => do
      let t ← programTermSyntaxOfProgramTerm t
      `(ProgramTerm.some $t)
  | .none => `(ProgramTerm.none)
  | .seq head tail => do
      let head ← programTermSyntaxOfProgramTerm head
      let tail ← tail.mapM programTermSyntaxOfProgramTerm
      let tail := tail.toArray
      `(ProgramTerm.seq $head [$tail,*])
  | .tuple xs => do
      let xs ← xs.mapM programTermSyntaxOfProgramTerm
      let xs := xs.toArray
      `(ProgramTerm.tuple [$xs,*])
  | .wrap label t => do
      let t ← programTermSyntaxOfProgramTerm t
      `(ProgramTerm.wrap $(Syntax.mkStrLit label) $t)

private def exprSyntaxOfExpr (e : _root_.Expr) : CommandElabM (TSyntax `term) := do
  let elems ← e.mapM termSyntaxOfTerm
  let elems := elems.toArray
  `([$elems,*])

private partial def atomSyntax : Syntax → CommandElabM (TSyntax `term × ProgramTerm)
  | `(program_atom| seq($atoms:program_atom,*)) => do
      let atoms := atoms.getElems.toList
      let headStx :: tailStxs := atoms
        | throwError "seq requires at least one element"
      let (_, headRuntime) ← atomSyntax headStx
      let tail ← tailStxs.mapM atomSyntax
      let runtime := ProgramTerm.seq headRuntime (tail.map Prod.snd)
      pure (← programTermSyntaxOfProgramTerm runtime, runtime)
  | `(program_atom| wrap($label:str, $arg:program_atom)) => do
      let (_, argRuntime) ← atomSyntax arg
      let runtime := ProgramTerm.wrap label.getString argRuntime
      pure (← programTermSyntaxOfProgramTerm runtime, runtime)
  | `(program_atom| wrap($label:ident, $arg:program_atom)) => do
      let (_, argRuntime) ← atomSyntax arg
      let runtime := ProgramTerm.wrap label.getId.getString! argRuntime
      pure (← programTermSyntaxOfProgramTerm runtime, runtime)
  | `(program_atom| $fn:ident($atoms:program_atom,*)) => do
      let atoms := atoms.getElems.toList
      match fn.getId.getString! with
      | "some" =>
          let [argStx] := atoms
            | throwErrorAt fn "some requires exactly one element"
          let (_, argRuntime) ← atomSyntax argStx
          let runtime := ProgramTerm.some argRuntime
          pure (← programTermSyntaxOfProgramTerm runtime, runtime)
      | "seq" =>
          let headStx :: tailStxs := atoms
            | throwErrorAt fn "seq requires at least one element"
          let (_, headRuntime) ← atomSyntax headStx
          let tail ← tailStxs.mapM atomSyntax
          let runtime := ProgramTerm.seq headRuntime (tail.map Prod.snd)
          pure (← programTermSyntaxOfProgramTerm runtime, runtime)
      | "tuple" =>
          let parsed ← atoms.mapM atomSyntax
          let runtime := ProgramTerm.tuple (parsed.map Prod.snd)
          pure (← programTermSyntaxOfProgramTerm runtime, runtime)
      | _ => throwErrorAt fn "unsupported program atom function"
  | `(program_atom| @$n:num) => do
      let n ← numLit! n
      pure (← `(ProgramTerm.index $(Syntax.mkNumLit (toString n))), ProgramTerm.index n)
  | `(program_atom| $n:num) => do
      let n ← numLit! n
      let t := _root_.Term.nat n
      pure (← programTermSyntaxOfTerm t, ProgramTerm.term t)
  | `(program_atom| $s:str) => do
      let t := _root_.Term.str s.getString
      pure (← programTermSyntaxOfTerm t, ProgramTerm.term t)
  | `(program_atom| {$t:term}) => do
      pure (← `(ProgramTerm.term $t), ProgramTerm.term Term.none)
  | `(program_atom| $id:ident) => do
      let name := id.getId.getString!
      if name = "none" then
        pure (← `(ProgramTerm.none), ProgramTerm.none)
      else
        let t := _root_.Term.op name
        pure (← programTermSyntaxOfTerm t, ProgramTerm.term t)
  | stx => throwErrorAt stx "unsupported program atom"

private def stepSyntax : Syntax → CommandElabM (TSyntax `term × ProgramExpr)
  | `(program_step| [$atoms:program_atom,*]) => do
      let parsed ← atoms.getElems.mapM atomSyntax
      let elems := parsed.map Prod.fst
      let runtime := parsed.toList.map Prod.snd
      pure (← `([$elems,*]), runtime)
  | stx => throwErrorAt stx "unsupported program step"

private def contextDeclSyntax : Syntax → CommandElabM (String × TSyntax `term)
  | `(program_context_decl| $name:ident : $τ:program_ty) => do
      pure (name.getId.getString!, ← tySyntax τ)
  | stx => throwErrorAt stx "unsupported context declaration"

private def mkInternalName (base suffix : Name) : Name :=
  Name.mkSimple s!"program_{base.getString!}_{suffix.getString!}"

private def mkContextBody (decls : Array (String × TSyntax `term)) :
    CommandElabM (TSyntax `term) := do
  let nameId := mkIdent `name
  let mut body ← `(Option.none)
  for (op, τ) in decls.reverse do
    let opLit := Syntax.mkStrLit op
    body ← `(if $nameId = $opLit then some $τ else $body)
  `(fun $nameId => $body)

private unsafe def evalConstAs (α : Type) (typeExpr : Lean.Expr) (valueName : Name) :
    CommandElabM α := do
  liftTermElabM <| Lean.Elab.Term.evalTerm α typeExpr (mkIdent valueName)

private unsafe def evalConst (α : Type) (typeName valueName : Name) : CommandElabM α :=
  evalConstAs α (mkConst typeName) valueName

private def resolveProgramForManual (evalOp : EvalOpEngine) (Γ : _root_.Context)
    (p : Program) : Except String (Array (_root_.Expr × _root_.Term)) :=
  go 0 [] #[]
where
  go (idx : Nat) (acc : List _root_.Term) (out : Array (_root_.Expr × _root_.Term)) :
      Except String (Array (_root_.Expr × _root_.Term)) :=
    if hidx : idx < p.length then
      let pExpr := p.get ⟨idx, hidx⟩
      match ProgramExpr.resolve acc pExpr with
      | none => .error s!"failed to resolve program expression at index {idx}"
      | some e =>
          match _root_.candidateValues evalOp Γ e with
          | v :: _ => go (idx + 1) (acc ++ [v]) (out.push (e, v))
          | [] => .error s!"no candidate values were produced at index {idx}"
    else
      .ok out
  termination_by p.length - idx

private def manualAltData (resolved : Array (_root_.Expr × _root_.Term)) (stx : Syntax) :
    CommandElabM (Nat × _root_.Expr × _root_.Term × TSyntax `term) := do
  match stx with
  | `(program_manual_alt| | $n:num => $proof:term) => do
      let idx ← numLit! n
      let some (e, v) := resolved[idx]?
        | throwErrorAt n "manual proof index {idx} is outside the program"
      pure (idx, e, v, proof)
  | stx => throwErrorAt stx "unsupported manual proof clause"

private partial def mkManualBody (entries : List (Nat × _root_.Expr × _root_.Term × TSyntax `term)) :
    CommandElabM (TSyntax `term) := do
  match entries with
  | [] => `(none)
  | (idx, e, v, proof) :: rest => do
      let rest ← mkManualBody rest
      let e ← exprSyntaxOfExpr e
      let v ← termSyntaxOfTerm v
      `(if idx = $(Syntax.mkNumLit (toString idx)) then
          if h : e = $e then
            some ⟨$v, by
              subst e
              exact $proof⟩
          else none
        else $rest)

private def latestCurrentModule? (env : Environment) (mainModule : Name) :
    Option ProgramModuleInfo :=
  (programModuleExt.getState env).toList.reverse.find? (fun info => info.mainModule == mainModule)

elab_rules : command
  | `(program_module $modName:ident where
      context
      $ctxDecls:program_context_decl*
      engine
      $engineTerm:term
      program
      $steps:program_step*
      $[manual_proofs
      $manualAlts:program_manual_alt*]?
      end) => unsafe do
    let mainModule ← getMainModule
    if let some _ := latestCurrentModule? (← getEnv) mainModule then
      throwErrorAt modName "only one program_module is allowed per source file"

    let userName := modName.getId
    let ctxName := mkInternalName userName `context
    let evalName := mkInternalName userName `eval
    let programName := mkInternalName userName `program
    let manualName := mkInternalName userName `manual

    let ctxDecls ← ctxDecls.mapM contextDeclSyntax
    let ctxBody ← mkContextBody ctxDecls
    elabCommand (← `(def $(mkIdent ctxName) : _root_.Context := $ctxBody))
    elabCommand (← `(def $(mkIdent evalName) : EvalOpEngine := $engineTerm))

    let steps ← steps.mapM stepSyntax
    let stepTerms := steps.map Prod.fst
    elabCommand (← `(def $(mkIdent programName) : Program := [$stepTerms,*]))

    let evalOp ← evalConst EvalOpEngine ``EvalOpEngine evalName
    let Γ ← evalConst _root_.Context (Name.mkSimple "Context") ctxName
    let runtimeProgram ← evalConst Program ``Program programName
    let manualName? ←
      match manualAlts with
      | none => pure none
      | some manualAlts => do
          let resolved ←
            match resolveProgramForManual evalOp Γ runtimeProgram with
            | .ok resolved => pure resolved
            | .error msg => throwError msg
          let entries ← manualAlts.mapM (manualAltData resolved)
          let body ← mkManualBody entries.toList
          elabCommand (← `(def $(mkIdent manualName) :
              Program.ManualProofProvider $(mkIdent evalName) $(mkIdent ctxName) :=
            fun idx e => $body))
          pure (some manualName)

    modifyEnv (programModuleExt.addEntry · {
      mainModule := mainModule
      userName := userName
      contextName := ctxName
      evalName := evalName
      programName := programName
      manualName? := manualName?
    })

elab_rules : command
  | `(#run_program) => unsafe do
    let mainModule ← getMainModule
    let some info := latestCurrentModule? (← getEnv) mainModule
      | throwError "#run_program requires a preceding program_module in this source file"
    let evalOp ← evalConst EvalOpEngine ``EvalOpEngine info.evalName
    let Γ ← evalConst _root_.Context (Name.mkSimple "Context") info.contextName
    let p ← evalConst Program ``Program info.programName
    let manual ←
      match info.manualName? with
      | some manualName =>
          evalConstAs (Program.ManualProofProvider evalOp Γ)
            (mkApp2 (mkConst ``Program.ManualProofProvider) (mkConst info.evalName) (mkConst info.contextName))
            manualName
      | none =>
          pure (Program.noManualProofs evalOp Γ)
    let result ← liftTermElabM <|
      Program.eval evalOp Γ (mkConst info.evalName) (mkConst info.contextName) p manual
    match result with
    | .ok values => logInfo m!"{repr values}"
    | .error err =>
        match err.resolveError?, err.proofError? with
        | some msg, _ => throwError msg
        | _, some msg => throwError "program evaluation failed at index {err.idx}: {msg}"
        | _, _ => throwError "program evaluation failed at index {err.idx}: {repr err}"

end ProgramDsl
