import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Basic

inductive Ty where
  | nat
  | str
  | option : Ty → Ty
  | seq : Ty → Ty
  | tuple : List Ty → Ty
  | nominal : String → Ty → Ty
  | arrow : List Ty → Ty → Ty
deriving Repr

mutual
  def Ty.decEq : (a b : Ty) → Decidable (a = b)
    | .nat, .nat => isTrue rfl
    | .str, .str => isTrue rfl
    | .option τ₁, .option τ₂ =>
        match Ty.decEq τ₁ τ₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .seq τ₁, .seq τ₂ =>
        match Ty.decEq τ₁ τ₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .tuple τs₁, .tuple τs₂ =>
        match Ty.listDecEq τs₁ τs₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .nominal label₁ τ₁, .nominal label₂ τ₂ =>
        match (inferInstance : Decidable (label₁ = label₂)), Ty.decEq τ₁ τ₂ with
        | isTrue h_label, isTrue h_ty => isTrue (by cases h_label; cases h_ty; rfl)
        | isFalse h_label, _ =>
            isFalse (by intro h_eq; cases h_eq; exact h_label rfl)
        | _, isFalse h_ty =>
            isFalse (by intro h_eq; cases h_eq; exact h_ty rfl)
    | .arrow args₁ out₁, .arrow args₂ out₂ =>
        match Ty.listDecEq args₁ args₂, Ty.decEq out₁ out₂ with
        | isTrue h_args, isTrue h_out => isTrue (by cases h_args; cases h_out; rfl)
        | isFalse h_args, _ =>
            isFalse (by intro h_eq; cases h_eq; exact h_args rfl)
        | _, isFalse h_out =>
            isFalse (by intro h_eq; cases h_eq; exact h_out rfl)
    | .nat, .str
    | .nat, .option _
    | .nat, .seq _
    | .nat, .tuple _
    | .nat, .nominal _ _
    | .nat, .arrow _ _
    | .str, .nat
    | .str, .option _
    | .str, .seq _
    | .str, .tuple _
    | .str, .nominal _ _
    | .str, .arrow _ _
    | .option _, .nat
    | .option _, .str
    | .option _, .seq _
    | .option _, .tuple _
    | .option _, .nominal _ _
    | .option _, .arrow _ _
    | .seq _, .nat
    | .seq _, .str
    | .seq _, .option _
    | .seq _, .tuple _
    | .seq _, .nominal _ _
    | .seq _, .arrow _ _
    | .tuple _, .nat
    | .tuple _, .str
    | .tuple _, .option _
    | .tuple _, .seq _
    | .tuple _, .nominal _ _
    | .tuple _, .arrow _ _
    | .nominal _ _, .nat
    | .nominal _ _, .str
    | .nominal _ _, .option _
    | .nominal _ _, .seq _
    | .nominal _ _, .tuple _
    | .nominal _ _, .arrow _ _
    | .arrow _ _, .nat
    | .arrow _ _, .str
    | .arrow _ _, .option _
    | .arrow _ _, .seq _
    | .arrow _ _, .tuple _
    | .arrow _ _, .nominal _ _ => isFalse (by intro h; cases h)

  def Ty.listDecEq : (a b : List Ty) → Decidable (a = b)
    | [], [] => isTrue rfl
    | τ₁ :: τs₁, τ₂ :: τs₂ =>
        match Ty.decEq τ₁ τ₂, Ty.listDecEq τs₁ τs₂ with
        | isTrue h_head, isTrue h_tail =>
            isTrue (by cases h_head; cases h_tail; rfl)
        | isFalse h_head, _ =>
            isFalse (by intro h_eq; cases h_eq; exact h_head rfl)
        | _, isFalse h_tail =>
            isFalse (by intro h_eq; cases h_eq; exact h_tail rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Ty := Ty.decEq

def Context := String → Option Ty

inductive Term where
  | nat : Nat → Term
  | str : String → Term
  | none
  | some : Term → Term
  | seqVal : Term → List Term → Term
  | tupleVal : List Term → Term
  | op : String → Term
  | wrap : String → Term → Term
deriving Repr

mutual
  def Term.decEq : (a b : Term) → Decidable (a = b)
    | .nat n₁, .nat n₂ =>
        match (inferInstance : Decidable (n₁ = n₂)) with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .str s₁, .str s₂ =>
        match (inferInstance : Decidable (s₁ = s₂)) with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .none, .none => isTrue rfl
    | .some t₁, .some t₂ =>
        match Term.decEq t₁ t₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .seqVal head₁ tail₁, .seqVal head₂ tail₂ =>
        match Term.decEq head₁ head₂, Term.listDecEq tail₁ tail₂ with
        | isTrue h_head, isTrue h_tail =>
            isTrue (by cases h_head; cases h_tail; rfl)
        | isFalse h_head, _ =>
            isFalse (by intro h_eq; cases h_eq; exact h_head rfl)
        | _, isFalse h_tail =>
            isFalse (by intro h_eq; cases h_eq; exact h_tail rfl)
    | .tupleVal ts₁, .tupleVal ts₂ =>
        match Term.listDecEq ts₁ ts₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .op name₁, .op name₂ =>
        match (inferInstance : Decidable (name₁ = name₂)) with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h_eq; cases h_eq; exact h rfl)
    | .wrap label₁ t₁, .wrap label₂ t₂ =>
        match (inferInstance : Decidable (label₁ = label₂)), Term.decEq t₁ t₂ with
        | isTrue h_label, isTrue h_term =>
            isTrue (by cases h_label; cases h_term; rfl)
        | isFalse h_label, _ =>
            isFalse (by intro h_eq; cases h_eq; exact h_label rfl)
        | _, isFalse h_term =>
            isFalse (by intro h_eq; cases h_eq; exact h_term rfl)
    | .nat _, .str _
    | .nat _, .none
    | .nat _, .some _
    | .nat _, .seqVal _ _
    | .nat _, .tupleVal _
    | .nat _, .op _
    | .nat _, .wrap _ _
    | .str _, .nat _
    | .str _, .none
    | .str _, .some _
    | .str _, .seqVal _ _
    | .str _, .tupleVal _
    | .str _, .op _
    | .str _, .wrap _ _
    | .none, .nat _
    | .none, .str _
    | .none, .some _
    | .none, .seqVal _ _
    | .none, .tupleVal _
    | .none, .op _
    | .none, .wrap _ _
    | .some _, .nat _
    | .some _, .str _
    | .some _, .none
    | .some _, .seqVal _ _
    | .some _, .tupleVal _
    | .some _, .op _
    | .some _, .wrap _ _
    | .seqVal _ _, .nat _
    | .seqVal _ _, .str _
    | .seqVal _ _, .none
    | .seqVal _ _, .some _
    | .seqVal _ _, .tupleVal _
    | .seqVal _ _, .op _
    | .seqVal _ _, .wrap _ _
    | .tupleVal _, .nat _
    | .tupleVal _, .str _
    | .tupleVal _, .none
    | .tupleVal _, .some _
    | .tupleVal _, .seqVal _ _
    | .tupleVal _, .op _
    | .tupleVal _, .wrap _ _
    | .op _, .nat _
    | .op _, .str _
    | .op _, .none
    | .op _, .some _
    | .op _, .seqVal _ _
    | .op _, .tupleVal _
    | .op _, .wrap _ _
    | .wrap _ _, .nat _
    | .wrap _ _, .str _
    | .wrap _ _, .none
    | .wrap _ _, .some _
    | .wrap _ _, .seqVal _ _
    | .wrap _ _, .tupleVal _
    | .wrap _ _, .op _ => isFalse (by intro h; cases h)

  def Term.listDecEq : (a b : List Term) → Decidable (a = b)
    | [], [] => isTrue rfl
    | t₁ :: ts₁, t₂ :: ts₂ =>
        match Term.decEq t₁ t₂, Term.listDecEq ts₁ ts₂ with
        | isTrue h_head, isTrue h_tail =>
            isTrue (by cases h_head; cases h_tail; rfl)
        | isFalse h_head, _ =>
            isFalse (by intro h_eq; cases h_eq; exact h_head rfl)
        | _, isFalse h_tail =>
            isFalse (by intro h_eq; cases h_eq; exact h_tail rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Term := Term.decEq

abbrev Expr := List Term

def EvalOpEngine := String → Expr → Option Term

namespace Term

/-- `op` is only a top-level active operator marker. It is not a bag value. -/
abbrev isOp : Term → Bool := λ term => if let Term.op _ := term then true else false
abbrev isNonOp : Term → Bool := λ term => !term.isOp

/- A recursive syntactic check that rejects operators anywhere inside a bag value. -/
mutual
  @[simp] def noOps : Term → Bool
    | Term.op .. => false
    | Term.nat _ => true
    | Term.str _ => true
    | Term.none => true
    | Term.some t => t.noOps
    | Term.seqVal head tail => noOps head && noOpsList tail
    | Term.tupleVal ts => noOpsList ts
    | Term.wrap _ t => t.noOps

  @[simp] def noOpsList : List Term → Bool
    | [] => true
    | t :: ts => t.noOps && noOpsList ts

end

/-- Boolean check that all types in a list equal the target type. -/
def allSameTy (τ : Ty) : List Ty → Bool
  | [] => true
  | τ' :: τs => if τ' = τ then allSameTy τ τs else false

@[simp] lemma allSameTy_replicate (τ : Ty) (n : Nat) :
    allSameTy τ (List.replicate n τ) := by
  induction n with
  | zero => simp [allSameTy]
  | succ n ih => simp [List.replicate, allSameTy, ih]

/- Context-free type extraction for bag arguments. -/
mutual
  @[simp] def typeOf : Term → Option Ty
    | Term.nat _ => Option.some Ty.nat
    | Term.str _ => Option.some Ty.str
    | Term.none => Option.none
    | Term.some t => do
        let τ ← t.typeOf
        Option.some (Ty.option τ)
    | Term.seqVal head tail => do
        let τ ← head.typeOf
        let τs ← typeOfList tail
        if allSameTy τ τs then
          Option.some (Ty.seq τ)
        else
          Option.none
    | Term.tupleVal ts => do
        let τs ← typeOfList ts
        Option.some (Ty.tuple τs)
    | Term.op .. => Option.none
    | Term.wrap label t =>
        match t.typeOf with
        | Option.some τ => Option.some (Ty.nominal label τ)
        | _ => Option.none

  @[simp] def typeOfList : List Term → Option (List Ty)
    | [] => Option.some []
    | t :: ts => do
        let τ ← t.typeOf
        let τs ← typeOfList ts
        Option.some (τ :: τs)

end

mutual
  @[simp] lemma noOps_of_typeOf_some {t : Term} {τ : Ty} :
      t.typeOf = Option.some τ → t.noOps := by
    cases t with
    | nat n =>
        intro _
        simp_all
    | str s =>
        intro _
        simp_all
    | none =>
        intro _
        simp_all
    | some t =>
        intro h
        simp_all
        cases h_inner : t.typeOf with
        | none =>
            simp_all
        | some τ_inner =>
            simp_all
            simpa [noOps] using noOps_of_typeOf_some (t := t) h_inner
    | op name =>
        intro _
        simp_all
    | wrap label t =>
        intro h
        simp [typeOf] at h
        cases h_inner : t.typeOf with
        | none =>
            simp [h_inner] at h
        | some τ_inner =>
            simp [h_inner] at h
            simpa [noOps] using noOps_of_typeOf_some (t := t) h_inner
    | tupleVal ts =>
        intro h
        simp [typeOf] at h
        cases h_types : typeOfList ts with
        | none =>
            simp [h_types] at h
        | some τs =>
            simp [noOps]
            exact noOpsList_of_typeOfList_some h_types
    | seqVal head tail =>
        intro h
        simp_all
        cases h_head : head.typeOf with
        | none =>
            simp_all
        | some τ_head =>
            cases h_tail : typeOfList tail with
            | none =>
                simp_all
            | some τs_tail =>
                constructor
                · simpa [Term.noOps] using (noOps_of_typeOf_some (t := head) h_head)
                · simpa [Term.noOpsList] using noOpsList_of_typeOfList_some h_tail

  @[simp] lemma noOpsList_of_typeOfList_some {ts : List Term} {τs : List Ty} :
      typeOfList ts = Option.some τs → noOpsList ts := by
    cases ts with
    | nil =>
        intro _
        simp_all
    | cons head tail =>
        intro _
        simp_all
        cases h_head : head.typeOf with
        | none =>
            simp_all
        | some τ_head =>
            cases h_tail : typeOfList tail with
            | none =>
                simp_all
            | some τs_tail =>
                constructor
                · simpa [Term.noOps] using (noOps_of_typeOf_some (t := head) h_head)
                · simpa [Term.noOpsList] using noOpsList_of_typeOfList_some h_tail
end

lemma seqVal_typeOf_sound {head : Term} {tail : List Term} {τ : Ty} :
    Term.typeOf (Term.seqVal head tail) = Option.some τ → ∃ elemTy, τ = Ty.seq elemTy := by
  simp_all; intro h
  cases h_head : head.typeOf with
  | none => simp_all
  | some τ_head =>
    cases h_tail : Term.typeOfList tail with
    | none => simp_all
    | some τs_tail => simp_all; exact ⟨τ_head, h.2.symm⟩

lemma seqVal_typeOf_complete {head : Term} {tail : List Term} {τ : Ty} :
    Term.typeOfList (head :: tail) = Option.some (List.replicate (head :: tail).length τ) →
    Term.typeOf (Term.seqVal head tail) = Option.some (Ty.seq τ) := by
  intro h_types
  simp_all
  cases h_head : head.typeOf with
  | none =>
      simp_all
  | some τ_head =>
      cases h_tail : Term.typeOfList tail with
      | none =>
          simp_all
      | some τs_tail =>
          simp_all
          cases h_types
          simp_all

lemma tupleVal_typeOf_sound {ts : List Term} {τ : Ty} :
    Term.typeOf (Term.tupleVal ts) = Option.some τ → ∃ elemTys, τ = Ty.tuple elemTys := by
  simp [Term.typeOf]; intro h
  cases h_types : Term.typeOfList ts with
  | none => simp_all
  | some τs => simp_all; cases h; exact ⟨τs, rfl⟩

lemma tupleVal_typeOf_complete {ts : List Term} {τs : List Ty} :
    Term.typeOfList ts = Option.some τs →
    Term.typeOf (Term.tupleVal ts) = Option.some (Ty.tuple τs) := by
  intro _
  simp_all

end Term

/-- Keep only operator terms from an expression. -/
def filterOps (e : Expr) : Expr := e.filter Term.isOp

/-- Keep only top-level non-operator terms from an expression. -/
def filterNonOps (e : Expr) : Expr := e.filter Term.isNonOp

/-- Predicate saying that an expression contains only opaque non-operator values. -/
def noOps (e : Expr) : Prop :=
  ∀ t ∈ e, t.noOps

lemma noOps_of_perm {xs ys : List Term} (h_perm : xs.Perm ys) :
    noOps ys → noOps xs :=
  fun h_noops t ht => h_noops t (h_perm.mem_iff.1 ht)

lemma noOps_of_mapM_typeOf {xs : List Term} {τs : List Ty}
    (h_map : xs.mapM Term.typeOf = some τs) :
    noOps xs := by
  intro t ht
  induction xs generalizing τs with
  | nil =>
      cases ht
  | cons head tail ih =>
      simp at ht
      simp at h_map
      cases h_head : head.typeOf with
      | none =>
          simp [h_head] at h_map
      | some τ_head =>
          cases h_tail : tail.mapM Term.typeOf with
          | none =>
              simp [h_head, h_tail] at h_map
          | some τs_tail =>
              simp [h_head, h_tail] at h_map
              rcases ht with rfl | ht_tail
              · exact Term.noOps_of_typeOf_some h_head
              · exact ih h_tail ht_tail

lemma filter_partition_perm (e : Expr) :
    (filterOps e ++ filterNonOps e).Perm e := by
  induction e with
  | nil => simp [filterOps, filterNonOps]
  | cons t ts ih =>
      cases t with
      | op name =>
          simpa [filterOps, filterNonOps, Term.isOp, Term.isNonOp] using
            List.Perm.cons (Term.op name) ih
      | _ =>
          exact ((List.perm_cons_append_cons _ (List.Perm.refl _)).symm).trans
            (List.Perm.cons _ ih)

/-- A `noOps` bag contributes no active operators to `filterOps`. -/
lemma filterOps_eq_nil_of_noOps {e : Expr} (h_noops : noOps e) :
    filterOps e = [] := by
  induction e with
  | nil => simp [filterOps]
  | cons head tail ih =>
      have h_head : head.noOps := h_noops head (by simp)
      have h_tail : noOps tail := fun t ht => h_noops t (by simp [ht])
      cases head with
      | op name => simp [Term.noOps] at h_head
      | _ => simpa [filterOps, Term.isOp] using ih h_tail

/-- Filtering non-operators from a `noOps` bag returns the bag unchanged. -/
lemma filterNonOps_eq_self_of_noOps {e : Expr} (h_noops : noOps e) :
    filterNonOps e = e := by
  induction e with
  | nil => simp [filterNonOps]
  | cons head tail ih =>
      have h_head : head.noOps := h_noops head (by simp)
      have h_tail : noOps tail := fun t ht => h_noops t (by simp [ht])
      cases head with
      | op name => simp [Term.noOps] at h_head
      | nat n => simpa [filterNonOps, Term.isNonOp] using congrArg (List.cons (Term.nat n)) (ih h_tail)
      | str s => simpa [filterNonOps, Term.isNonOp] using congrArg (List.cons (Term.str s)) (ih h_tail)
      | none => simpa [filterNonOps, Term.isNonOp] using congrArg (List.cons Term.none) (ih h_tail)
      | some t => simpa [filterNonOps, Term.isNonOp] using congrArg (List.cons (Term.some t)) (ih h_tail)
      | seqVal h tl => simpa [filterNonOps, Term.isNonOp] using congrArg (List.cons (Term.seqVal h tl)) (ih h_tail)
      | tupleVal ts => simpa [filterNonOps, Term.isNonOp] using congrArg (List.cons (Term.tupleVal ts)) (ih h_tail)
      | wrap l t => simpa [filterNonOps, Term.isNonOp] using congrArg (List.cons (Term.wrap l t)) (ih h_tail)

/-- Context-free inference for the restricted term language. -/
def inferType (Γ : Context) (t : Term) : Option Ty :=
  match t with
  | Term.op name => Γ name
  | _ => t.typeOf

mutual
  inductive AllTermTypes : Context → List Term → List Ty → Prop where
    | nil {Γ} :
        AllTermTypes Γ [] []
    | cons {Γ t ts τ τs} :
        TermType Γ t τ →
        AllTermTypes Γ ts τs →
        AllTermTypes Γ (t :: ts) (τ :: τs)

  inductive TermType : Context → Term → Ty → Prop where
    | t_nat {Γ n} :
        TermType Γ (Term.nat n) Ty.nat
    | t_str {Γ s} :
        TermType Γ (Term.str s) Ty.str
    | t_none {Γ τ} :
        TermType Γ Term.none (Ty.option τ)
    | t_some {Γ t τ} :
        TermType Γ t τ →
        TermType Γ (Term.some t) (Ty.option τ)
    | t_seq {Γ head tail τ} :
        AllTermTypes Γ (head :: tail) (List.replicate (head :: tail).length τ) →
        TermType Γ (Term.seqVal head tail) (Ty.seq τ)
    | t_tuple {Γ elems τs} :
        AllTermTypes Γ elems τs →
        TermType Γ (Term.tupleVal elems) (Ty.tuple τs)
    | t_wrap {Γ label t τ} :
        TermType Γ t τ →
        TermType Γ (Term.wrap label t) (Ty.nominal label τ)
    | t_op_bare {Γ name τs_expected τ_out} :
        (h_ctx : Γ name = some (Ty.arrow τs_expected τ_out)) →
        TermType Γ (Term.op name) (Ty.arrow τs_expected τ_out)
end

lemma allTermTypes_toForall₂ :
    {Γ : Context} → {args : List Term} → {τs : List Ty} →
    AllTermTypes Γ args τs → List.Forall₂ (TermType Γ) args τs
  | _, _, _, AllTermTypes.nil => List.Forall₂.nil
  | _, _, _, AllTermTypes.cons h_head h_tail =>
      List.Forall₂.cons h_head (allTermTypes_toForall₂ h_tail)

lemma allTermTypes_ofForall₂ {Γ : Context} {args : List Term} {τs : List Ty} :
    List.Forall₂ (TermType Γ) args τs → AllTermTypes Γ args τs := by
  intro h
  induction h with
  | nil => exact AllTermTypes.nil
  | cons h_head h_tail ih => exact AllTermTypes.cons h_head ih

mutual
  lemma termType_of_typeOf {Γ : Context} {t : Term} {τ : Ty} :
      t.typeOf = some τ → TermType Γ t τ := by
    cases t with
    | nat n =>
        intro h
        simp [Term.typeOf] at h
        cases h
        exact TermType.t_nat
    | str s =>
        intro h
        simp [Term.typeOf] at h
        cases h
        exact TermType.t_str
    | none =>
        intro h
        simp [Term.typeOf] at h
    | some inner =>
        intro h
        simp [Term.typeOf] at h
        cases h_inner : inner.typeOf with
        | none =>
            simp [h_inner] at h
        | some τ_inner =>
            simp [h_inner] at h
            cases h
            exact TermType.t_some (termType_of_typeOf h_inner)
    | op name =>
        intro h
        simp [Term.typeOf] at h
    | wrap label inner =>
        intro h
        simp [Term.typeOf] at h
        cases h_inner : inner.typeOf with
        | none =>
            simp [h_inner] at h
        | some τ_inner =>
            simp [h_inner] at h
            cases h
            exact TermType.t_wrap (termType_of_typeOf h_inner)
    | tupleVal elems =>
        intro h
        simp [Term.typeOf] at h
        cases h_elems : Term.typeOfList elems with
        | none =>
            simp [h_elems] at h
        | some τs =>
            simp [h_elems] at h
            cases h
            exact TermType.t_tuple (allTermTypes_of_typeOfList h_elems)
    | seqVal head tail =>
        intro h
        simp [Term.typeOf] at h
        cases h_head : head.typeOf with
        | none =>
            simp [h_head] at h
        | some τ_head =>
            cases h_tail : Term.typeOfList tail with
            | none =>
                simp [h_head, h_tail] at h
            | some τs_tail =>
                by_cases h_same : Term.allSameTy τ_head τs_tail
                · simp [h_head, h_tail, h_same] at h
                  cases h
                  exact TermType.t_seq (by
                    simpa [List.replicate] using
                      AllTermTypes.cons
                        (termType_of_typeOf h_head)
                        (allTermTypes_replicate_of_typeOfList_allSame h_tail h_same))
                · simp [h_head, h_tail, h_same] at h

  lemma allTermTypes_of_typeOfList {Γ : Context} {ts : List Term} {τs : List Ty} :
      Term.typeOfList ts = some τs → AllTermTypes Γ ts τs := by
    cases ts with
    | nil =>
        intro h
        simp [Term.typeOfList] at h
        cases h
        exact AllTermTypes.nil
    | cons head tail =>
        intro h
        simp [Term.typeOfList] at h
        cases h_head : head.typeOf with
        | none =>
            simp [h_head] at h
        | some τ_head =>
            cases h_tail : Term.typeOfList tail with
            | none =>
                simp [h_head, h_tail] at h
            | some τs_tail =>
                simp [h_head, h_tail] at h
                cases h
                exact AllTermTypes.cons
                  (termType_of_typeOf h_head)
                  (allTermTypes_of_typeOfList h_tail)

  lemma allTermTypes_replicate_of_typeOfList_allSame {Γ : Context}
      {ts : List Term} {τs : List Ty} {τ : Ty} :
      Term.typeOfList ts = some τs →
      Term.allSameTy τ τs →
      AllTermTypes Γ ts (List.replicate ts.length τ) := by
    cases ts with
    | nil =>
        intro h_types h_same
        exact AllTermTypes.nil
    | cons head tail =>
        intro h_types h_same
        simp [Term.typeOfList] at h_types
        cases h_head : head.typeOf with
        | none =>
            simp [h_head] at h_types
        | some τ_head =>
            cases h_tail : Term.typeOfList tail with
            | none =>
                simp [h_head, h_tail] at h_types
            | some τs_tail =>
                simp [h_head, h_tail] at h_types
                cases h_types
                simp [Term.allSameTy] at h_same
                rcases h_same with ⟨rfl, h_tail_same⟩
                simpa using
                  AllTermTypes.cons
                    (termType_of_typeOf h_head)
                    (allTermTypes_replicate_of_typeOfList_allSame h_tail h_tail_same)
end

/-!
Semantic ambiguity layer.

The definitions below describe the full semantic ambiguity class: every
ordered, well-typed call whose arguments are selected from
the non-operator bag. Extra bag elements are explicitly documented as unused residue
and omitted optional parameters as synthesized arguments.
-/

/-- Metadata for an argument inserted by synthesis rather than explicitly supplied. -/
structure SynthesizedArg where
  paramIndex : Nat
  term : Term
deriving Repr, DecidableEq

/-- Result of argument enumeration before attaching the operation name. -/
structure RealizedArgs where
  args : List Term
  unused : Multiset Term
  synthesized : List SynthesizedArg
deriving DecidableEq

/-- A realized operation call with one admissible realization of its arguments. -/
structure RealizedCall where
  opName : String
  realizedArgs : RealizedArgs
deriving DecidableEq

/- Helpers for brevity -/
abbrev realizedEvalName (rc : RealizedCall) : String := rc.opName
abbrev realizedEvalArgs (rc : RealizedCall) : List Term := rc.realizedArgs.args

@[reducible] private def decideBEqLawful {α : Type} [DecidableEq α] [inst : BEq α]
    (h : ∀ a b : α, @BEq.beq α inst a b = decide (a = b)) : @LawfulBEq α inst where
  eq_of_beq {a b} hab := of_decide_eq_true (h a b ▸ hab)
  rfl {a} := h a a ▸ of_decide_eq_self_eq_true a

instance : BEq Ty where
  beq a b := decide (a = b)

instance : LawfulBEq Ty := decideBEqLawful (fun _ _ => rfl)

instance : BEq Term where
  beq a b := decide (a = b)

instance : LawfulBEq Term := decideBEqLawful (fun _ _ => rfl)

instance : BEq SynthesizedArg where
  beq a b := decide (a = b)

instance : LawfulBEq SynthesizedArg := decideBEqLawful (fun _ _ => rfl)

instance : BEq RealizedArgs where
  beq a b := decide (a = b)

instance : LawfulBEq RealizedArgs := decideBEqLawful (fun _ _ => rfl)

instance : BEq RealizedCall where
  beq a b := decide (a = b)

instance : LawfulBEq RealizedCall := decideBEqLawful (fun _ _ => rfl)

def IsExact (rc : RealizedCall) : Prop :=
  rc.realizedArgs.unused = 0 ∧ rc.realizedArgs.synthesized = []

def IsProjectiveOnly (rc : RealizedCall) : Prop :=
  rc.realizedArgs.synthesized = []

abbrev SynthesizedWithinBounds (τs : List Ty) (xs : List SynthesizedArg) : Prop :=
  ∀ x, x ∈ xs → x.paramIndex < τs.length

abbrev SynthesizedDistinct (xs : List SynthesizedArg) : Prop :=
  (xs.map SynthesizedArg.paramIndex).Nodup

def SynthesizedWellFormed (τs : List Ty) (xs : List SynthesizedArg) : Prop :=
  SynthesizedWithinBounds τs xs ∧ SynthesizedDistinct xs

def PairwiseDistinctParamTypes (τs : List Ty) : Prop :=
  τs.Nodup

def HasDistinctParameterTypes (Γ : Context) (name : String) : Prop :=
  ∃ τs τ_out,
    Γ name = some (Ty.arrow τs τ_out) ∧
    PairwiseDistinctParamTypes τs

-- namespace PickAll
/-- Enumerate every way to remove one context-free term of type `τ` from a bag. -/
def pickAllExact (τ : Ty) : List Term → List (Term × List Term)
  | [] => []
  | t :: ts =>
      let restPicks := (pickAllExact τ ts).map (fun picked => (picked.1, t :: picked.2))
      if t.typeOf = some τ then
        (t, ts) :: restPicks
      else
        restPicks

def optionArgMatches (τ : Ty) (t : Term) : Bool :=
  decide (t = Term.none) || decide (t.typeOf = some (Ty.option τ))

/-- Executable typing evidence for realized argument lists. `none` is allowed
only at option-typed slots; every other argument carries a `Term.typeOf` result. -/
inductive AllExecutableTypes : List Term → List Ty → Prop where
  | nil :
      AllExecutableTypes [] []
  | none {τ : Ty} {args : List Term} {τs : List Ty} :
      AllExecutableTypes args τs →
      AllExecutableTypes (Term.none :: args) (Ty.option τ :: τs)
  | cons {arg : Term} {args : List Term} {τ : Ty} {τs : List Ty} :
      arg.typeOf = some τ →
      AllExecutableTypes args τs →
      AllExecutableTypes (arg :: args) (τ :: τs)

/-- Option-argument selection treats explicit `none` as a supplied argument. -/
def pickAllOption (τ : Ty) : List Term → List (Term × List Term)
  | [] => []
  | t :: ts =>
      let restPicks := (pickAllOption τ ts).map (fun picked => (picked.1, t :: picked.2))
      if optionArgMatches τ t then
        (t, ts) :: restPicks
      else
        restPicks

lemma pickAllExact_sound {τ : Ty} {bag rest : List Term} {arg : Term} :
    (arg, rest) ∈ pickAllExact τ bag →
      arg.typeOf = some τ ∧ (arg :: rest).Perm bag := by
  induction bag generalizing arg rest with
  | nil =>
      simp [pickAllExact]
  | cons head tail ih =>
      intro h_mem
      by_cases h_head : head.typeOf = some τ
      · simp [pickAllExact, h_head] at h_mem
        rcases h_mem with h_here | h_tail
        · rcases h_here with ⟨rfl, rfl⟩
          exact ⟨h_head, List.Perm.refl _⟩
        · rcases h_tail with ⟨picked, h_picked_mem, h_pair⟩
          cases h_pair
          rcases ih h_picked_mem with ⟨h_type, h_perm⟩
          exact ⟨h_type, (List.Perm.swap _ head _).symm.trans
            (List.Perm.cons head h_perm)⟩
      · simp [pickAllExact, h_head] at h_mem
        rcases h_mem with ⟨picked, h_picked_mem, h_pair⟩
        cases h_pair
        rcases ih h_picked_mem with ⟨h_type, h_perm⟩
        exact ⟨h_type, (List.Perm.swap _ head _).symm.trans
          (List.Perm.cons head h_perm)⟩

lemma pickAllExact_mem_of_mem_type {τ : Ty} {bag : List Term} {arg : Term} :
    arg ∈ bag →
    arg.typeOf = some τ →
    ∃ rest, (arg, rest) ∈ pickAllExact τ bag := by
  induction bag with
  | nil =>
      intro h_mem _
      simp at h_mem
  | cons head tail ih =>
      intro h_mem h_type
      by_cases h_eq : head = arg
      · subst head
        exact ⟨tail, by simp [pickAllExact, h_type]⟩
      · have h_tail_mem : arg ∈ tail := by
          simp at h_mem
          rcases h_mem with h_head | h_tail
          · exact False.elim (h_eq h_head.symm)
          · exact h_tail
        rcases ih h_tail_mem h_type with ⟨rest, h_rest⟩
        by_cases h_head_type : head.typeOf = some τ
        · refine ⟨head :: rest, ?_⟩
          simp [pickAllExact, h_head_type]
          exact Or.inr h_rest
        · refine ⟨head :: rest, ?_⟩
          simpa [pickAllExact, h_head_type] using h_rest

lemma pickAllExact_complete {τ : Ty} {bag rest : List Term} {arg : Term} :
    arg ∈ bag →
    arg.typeOf = some τ →
    (arg :: rest).Perm bag →
    ∃ rest', (arg, rest') ∈ pickAllExact τ bag ∧ rest'.Perm rest := by
  intro h_mem h_type h_perm
  rcases pickAllExact_mem_of_mem_type h_mem h_type with ⟨rest', h_pick⟩
  rcases pickAllExact_sound h_pick with ⟨_, h_pick_perm⟩
  exact ⟨rest', h_pick,
    List.Perm.cons_inv (h_pick_perm.trans h_perm.symm)⟩

lemma pickAllOption_sound {τ : Ty} {bag rest : List Term} {arg : Term} :
    (arg, rest) ∈ pickAllOption τ bag →
      optionArgMatches τ arg ∧ (arg :: rest).Perm bag := by
  induction bag generalizing arg rest with
  | nil =>
      simp [pickAllOption]
  | cons head tail ih =>
      intro h_mem
      by_cases h_head : optionArgMatches τ head
      · simp [pickAllOption, h_head] at h_mem
        rcases h_mem with h_here | h_tail
        · rcases h_here with ⟨rfl, rfl⟩
          exact ⟨h_head, List.Perm.refl _⟩
        · rcases h_tail with ⟨picked, h_picked_mem, h_pair⟩
          cases h_pair
          rcases ih h_picked_mem with ⟨h_match, h_perm⟩
          exact ⟨h_match, (List.Perm.swap _ head _).symm.trans
            (List.Perm.cons head h_perm)⟩
      · have h_head_false : optionArgMatches τ head = false := by
          exact Bool.eq_false_iff.2 h_head
        simp [pickAllOption, h_head_false] at h_mem
        rcases h_mem with ⟨picked, h_picked_mem, h_pair⟩
        cases h_pair
        rcases ih h_picked_mem with ⟨h_match, h_perm⟩
        exact ⟨h_match, (List.Perm.swap _ head _).symm.trans
          (List.Perm.cons head h_perm)⟩

lemma pickAllOption_mem_of_mem_match {τ : Ty} {bag : List Term} {arg : Term} :
    arg ∈ bag →
    optionArgMatches τ arg →
    ∃ rest, (arg, rest) ∈ pickAllOption τ bag := by
  induction bag with
  | nil =>
      intro h_mem _
      simp at h_mem
  | cons head tail ih =>
      intro h_mem h_match
      by_cases h_eq : head = arg
      · subst head
        exact ⟨tail, by simp [pickAllOption, h_match]⟩
      · have h_tail_mem : arg ∈ tail := by
          simp at h_mem
          rcases h_mem with h_head | h_tail
          · exact False.elim (h_eq h_head.symm)
          · exact h_tail
        rcases ih h_tail_mem h_match with ⟨rest, h_rest⟩
        by_cases h_head_match : optionArgMatches τ head
        · refine ⟨head :: rest, ?_⟩
          simp [pickAllOption, h_head_match]
          exact Or.inr h_rest
        · have h_head_false : optionArgMatches τ head = false := by
            exact Bool.eq_false_iff.2 h_head_match
          refine ⟨head :: rest, ?_⟩
          simpa [pickAllOption, h_head_false] using h_rest

lemma pickAllOption_complete {τ : Ty} {bag rest : List Term} {arg : Term} :
    arg ∈ bag →
    optionArgMatches τ arg →
    (arg :: rest).Perm bag →
    ∃ rest', (arg, rest') ∈ pickAllOption τ bag ∧ rest'.Perm rest := by
  intro h_mem h_match h_perm
  rcases pickAllOption_mem_of_mem_match h_mem h_match with ⟨rest', h_pick⟩
  rcases pickAllOption_sound h_pick with ⟨_, h_pick_perm⟩
  exact ⟨rest', h_pick,
    List.Perm.cons_inv (h_pick_perm.trans h_perm.symm)⟩

lemma pickAllOption_eq_nil_iff {τ : Ty} {bag : List Term} :
    pickAllOption τ bag = [] ↔
      ∀ t, t ∈ bag → optionArgMatches τ t = false := by
  constructor
  · intro h_nil t ht
    by_cases h_match : optionArgMatches τ t
    · rcases pickAllOption_mem_of_mem_match ht h_match with ⟨rest, h_pick⟩
      rw [h_nil] at h_pick
      simp at h_pick
    · exact Bool.eq_false_iff.2 h_match
  · intro h_absent
    apply List.eq_nil_iff_forall_not_mem.2
    intro picked h_pick
    rcases picked with ⟨arg, rest⟩
    rcases pickAllOption_sound h_pick with ⟨h_match, h_perm⟩
    have h_arg_mem : arg ∈ bag :=
      (List.Perm.mem_iff h_perm).1 (by simp)
    rw [h_absent arg h_arg_mem] at h_match
    simp at h_match

lemma pickAllOption_eq_nil_of_perm {τ : Ty} {bag₁ bag₂ : List Term} :
    pickAllOption τ bag₁ = [] →
    bag₁.Perm bag₂ →
    pickAllOption τ bag₂ = [] := by
  intro h_nil h_perm; rw [pickAllOption_eq_nil_iff] at h_nil ⊢
  exact fun t ht => h_nil t (h_perm.mem_iff.2 ht)
-- end PickAll

/-- Realized argument enumeration with zero-based synthesized parameter metadata. -/
def enumerateRealizedArgsFrom : Nat → List Ty → List Term →
    List RealizedArgs
  -- nullary
  | _, [], bagArgs => [RealizedArgs.mk [] (bagArgs : Multiset Term) []]
  -- option type next
  | i, Ty.option τ :: expected, bagArgs =>
      let picks := pickAllOption τ bagArgs
      picks.flatMap
        (fun picked =>
          (enumerateRealizedArgsFrom (i + 1) expected picked.2).map
            (fun ra => RealizedArgs.mk (picked.1 :: ra.args) ra.unused ra.synthesized))
      ++
      (if picks = [] then
      (enumerateRealizedArgsFrom (i + 1) expected bagArgs).map
        (fun ra =>
          RealizedArgs.mk (Term.none :: ra.args) ra.unused
            ({ paramIndex := i, term := Term.none } :: ra.synthesized)) else [])
  -- non-option type next
  | i, τ :: expected, bagArgs =>
      (pickAllExact τ bagArgs).flatMap
        (fun picked =>
          (enumerateRealizedArgsFrom (i + 1) expected picked.2).map
            (fun ra => RealizedArgs.mk (picked.1 :: ra.args) ra.unused ra.synthesized))

def enumerateRealizedArgs (expected : List Ty) (bagArgs : List Term) :
    List RealizedArgs :=
  enumerateRealizedArgsFrom 0 expected bagArgs

lemma enumerateRealizedArgsFrom_synth_index_range
    {i : Nat} {expected : List Ty} {bagArgs : List Term} {ra : RealizedArgs} :
    ra ∈ enumerateRealizedArgsFrom i expected bagArgs →
      (∀ x, x ∈ ra.synthesized → i ≤ x.paramIndex ∧
        x.paramIndex < i + expected.length) ∧
      (ra.synthesized.map SynthesizedArg.paramIndex).Nodup := by
  induction expected generalizing i bagArgs ra with
  | nil =>
      intro h
      simp [enumerateRealizedArgsFrom] at h
      subst ra
      constructor
      · intro x hx
        simp at hx
      · simp
  | cons τ expected ih =>
      cases τ with
      | option τ_inner =>
          intro h
          by_cases h_picks : pickAllOption τ_inner bagArgs = []
          · simp [enumerateRealizedArgsFrom, h_picks] at h
            rcases h with ⟨tail, h_result, h_eq⟩
            subst ra
            rcases ih h_result with ⟨h_bounds, h_nodup⟩
            constructor
            · intro x hx
              simp at hx
              rcases hx with hx | hx
              · subst x
                simp
              · rcases h_bounds x hx with ⟨h_lo, h_hi⟩
                constructor
                · omega
                · have : x.paramIndex < i + expected.length + 1 := by omega
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
            · change (i :: tail.synthesized.map SynthesizedArg.paramIndex).Nodup
              rw [List.nodup_cons]
              constructor
              · intro h_mem
                rcases List.mem_map.1 h_mem with ⟨x, hx_tail, hx_eq⟩
                rcases h_bounds x hx_tail with ⟨h_lo, _⟩
                omega
              · exact h_nodup
          · simp [enumerateRealizedArgsFrom, h_picks] at h
            rcases h with ⟨arg, rest, _h_pick, tail, h_result, h_eq⟩
            subst ra
            rcases ih h_result with ⟨h_bounds, h_nodup⟩
            constructor
            · intro x hx
              rcases h_bounds x hx with ⟨h_lo, h_hi⟩
              constructor
              · omega
              · have : x.paramIndex < i + expected.length + 1 := by omega
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
            · exact h_nodup
      | _ =>
          intro h
          simp [enumerateRealizedArgsFrom] at h
          rcases h with ⟨arg, rest, _h_pick, tail, h_result, h_eq⟩
          subst ra
          rcases ih h_result with ⟨h_bounds, h_nodup⟩
          refine ⟨fun x hx => ?_, h_nodup⟩
          rcases h_bounds x hx with ⟨h_lo, h_hi⟩
          constructor
          · omega
          · have : x.paramIndex < i + expected.length + 1 := by omega
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

lemma enumerateRealizedArgsFrom_of_perm
    {i : Nat} {expected : List Ty} {bag₁ bag₂ : List Term} {ra : RealizedArgs}
    (h_perm : bag₁.Perm bag₂) :
    ra ∈ enumerateRealizedArgsFrom i expected bag₁ →
    ra ∈ enumerateRealizedArgsFrom i expected bag₂ := by
  induction expected generalizing i bag₁ bag₂ ra with
  | nil =>
      intro h
      simp [enumerateRealizedArgsFrom] at h ⊢
      subst ra
      have h_ms : (bag₁ : Multiset Term) = (bag₂ : Multiset Term) :=
        Quot.sound h_perm
      simp [h_ms]
  | cons τ expected ih =>
      cases τ with
      | option τ_inner =>
          intro h
          by_cases h_picks₁ : pickAllOption τ_inner bag₁ = []
          · have h_picks₂ : pickAllOption τ_inner bag₂ = [] :=
              pickAllOption_eq_nil_of_perm h_picks₁ h_perm
            simp [enumerateRealizedArgsFrom, h_picks₁] at h
            rcases h with ⟨tail, h_tail, h_eq⟩
            subst ra
            have h_tail₂ := ih h_perm h_tail
            simp [enumerateRealizedArgsFrom, h_picks₂]
            exact ⟨tail, h_tail₂, by simp⟩
          · simp [enumerateRealizedArgsFrom, h_picks₁] at h
            rcases h with ⟨arg, rest₁, h_pick₁, tail, h_tail, h_eq⟩
            subst ra
            rcases pickAllOption_sound h_pick₁ with ⟨h_match, h_pick_perm₁⟩
            have h_arg_mem₂ : arg ∈ bag₂ :=
              (List.Perm.mem_iff (h_pick_perm₁.trans h_perm)).1 (by simp)
            rcases pickAllOption_complete h_arg_mem₂ h_match
                (h_pick_perm₁.trans h_perm) with
              ⟨rest₂, h_pick₂, h_rest_perm⟩
            have h_tail₂ := ih h_rest_perm.symm h_tail
            have h_picks₂_ne : ¬pickAllOption τ_inner bag₂ = [] := by
              intro h_nil₂
              rw [pickAllOption_eq_nil_iff] at h_nil₂
              rw [h_nil₂ arg h_arg_mem₂] at h_match
              simp at h_match
            simp [enumerateRealizedArgsFrom, h_picks₂_ne]
            exact ⟨rest₂, h_pick₂, tail, h_tail₂, by simp⟩
      | _ =>
          intro h
          simp [enumerateRealizedArgsFrom] at h
          rcases h with ⟨arg, rest₁, h_pick₁, tail, h_tail, h_eq⟩
          subst ra
          rcases pickAllExact_sound h_pick₁ with ⟨h_type, h_pick_perm₁⟩
          have h_arg_mem₂ : arg ∈ bag₂ :=
            (List.Perm.mem_iff (h_pick_perm₁.trans h_perm)).1 (by simp)
          rcases pickAllExact_complete h_arg_mem₂ h_type
              (h_pick_perm₁.trans h_perm) with
            ⟨rest₂, h_pick₂, h_rest_perm⟩
          have h_tail₂ := ih h_rest_perm.symm h_tail
          simp [enumerateRealizedArgsFrom]
          exact ⟨rest₂, h_pick₂, tail, h_tail₂, by simp⟩

/--
Relational realized-argument selection for a signature suffix.

The relation records the ordered argument list, the final unconsumed bag, and
metadata for omitted optional parameters. Explicit `none` is a supplied option
argument; synthesized metadata is emitted only when no explicit option argument
is available for that slot.
-/
inductive RealizedArgsSelectionFrom :
    Nat → List Ty → List Term → List Term → Multiset Term → List SynthesizedArg → Prop where
  | nil {i : Nat} {bag : List Term} :
      RealizedArgsSelectionFrom i [] bag [] (bag : Multiset Term) []
  | option_supplied {i : Nat} {τ : Ty} {expected : List Ty}
      {bag rest args : List Term}
      {unused : Multiset Term} {synthesized : List SynthesizedArg} {arg : Term} :
      optionArgMatches τ arg = true →
      (arg :: rest).Perm bag →
      RealizedArgsSelectionFrom (i + 1) expected rest args unused synthesized →
      RealizedArgsSelectionFrom i (Ty.option τ :: expected) bag
        (arg :: args) unused synthesized
  | option_omitted {i : Nat} {τ : Ty} {expected : List Ty}
      {bag args : List Term}
      {unused : Multiset Term} {synthesized : List SynthesizedArg} :
      (∀ t, t ∈ bag → optionArgMatches τ t = false) →
      RealizedArgsSelectionFrom (i + 1) expected bag args unused synthesized →
      RealizedArgsSelectionFrom i (Ty.option τ :: expected) bag
        (Term.none :: args) unused
        ({ paramIndex := i, term := Term.none } :: synthesized)
  | required {i : Nat} {τ : Ty} {expected : List Ty}
      {bag rest args : List Term}
      {unused : Multiset Term} {synthesized : List SynthesizedArg} {arg : Term} :
      (λx => if let Ty.option _ := x then False else True) τ →
      arg.typeOf = some τ →
      (arg :: rest).Perm bag →
      RealizedArgsSelectionFrom (i + 1) expected rest args unused synthesized →
      RealizedArgsSelectionFrom i (τ :: expected) bag
        (arg :: args) unused synthesized

abbrev RealizedArgsSelection (expected : List Ty) (bag args : List Term)
    (unused : Multiset Term) (synthesized : List SynthesizedArg) : Prop :=
  RealizedArgsSelectionFrom 0 expected bag args unused synthesized

namespace RealizedArgsSelectionFrom

lemma of_perm
    {i : Nat} {expected : List Ty} {bag₁ bag₂ args : List Term} {unused : Multiset Term}
    {synthesized : List SynthesizedArg}
    (h_perm : bag₁.Perm bag₂) :
    RealizedArgsSelectionFrom i expected bag₁ args unused synthesized →
    RealizedArgsSelectionFrom i expected bag₂ args unused synthesized := by
  intro h
  induction h generalizing bag₂ with
  | nil =>
      rename_i i bag
      have h_ms : (bag : Multiset Term) = (bag₂ : Multiset Term) :=
        Quot.sound h_perm
      simpa [h_ms] using (RealizedArgsSelectionFrom.nil (i := i) (bag := bag₂))
  | option_supplied h_match h_arg_perm h_tail ih =>
      exact RealizedArgsSelectionFrom.option_supplied h_match
        (h_arg_perm.trans h_perm) h_tail
  | option_omitted h_absent h_tail ih =>
      refine RealizedArgsSelectionFrom.option_omitted ?_ (ih h_perm)
      intro t ht
      exact h_absent t ((List.Perm.mem_iff h_perm).2 ht)
  | required h_not_option h_type h_arg_perm h_tail ih =>
      exact RealizedArgsSelectionFrom.required h_not_option h_type
        (h_arg_perm.trans h_perm) h_tail

theorem sound
    {i : Nat} {expected : List Ty} {bag : List Term} {ra : RealizedArgs} :
    ra ∈ enumerateRealizedArgsFrom i expected bag →
      RealizedArgsSelectionFrom i expected bag ra.args ra.unused ra.synthesized := by
  induction expected generalizing i bag ra with
  | nil =>
      intro h
      simp [enumerateRealizedArgsFrom] at h
      subst ra
      exact RealizedArgsSelectionFrom.nil
  | cons τ expected ih =>
      cases τ with
      | option τ_inner =>
          intro h
          by_cases h_picks : pickAllOption τ_inner bag = []
          · simp [enumerateRealizedArgsFrom, h_picks] at h
            rcases h with ⟨tail, h_tail, h_eq⟩
            subst ra
            exact RealizedArgsSelectionFrom.option_omitted
              (pickAllOption_eq_nil_iff.1 h_picks) (ih h_tail)
          · simp [enumerateRealizedArgsFrom, h_picks] at h
            rcases h with ⟨arg, rest, h_pick, tail, h_tail, h_eq⟩
            subst ra
            rcases pickAllOption_sound h_pick with ⟨h_match, h_perm⟩
            exact RealizedArgsSelectionFrom.option_supplied h_match h_perm (ih h_tail)
      | _ =>
          intro h
          simp [enumerateRealizedArgsFrom] at h
          rcases h with ⟨arg, rest, h_pick, tail, h_tail, h_eq⟩
          subst ra
          rcases pickAllExact_sound h_pick with ⟨h_type, h_perm⟩
          exact RealizedArgsSelectionFrom.required (by simp) h_type h_perm (ih h_tail)

theorem complete
    {i : Nat} {expected : List Ty} {bag args : List Term} {unused : Multiset Term}
    {synthesized : List SynthesizedArg} :
    RealizedArgsSelectionFrom i expected bag args unused synthesized →
      RealizedArgs.mk args unused synthesized ∈
        enumerateRealizedArgsFrom i expected bag := by
  intro h
  induction h with
  | nil =>
      simp [enumerateRealizedArgsFrom]
  | option_supplied h_match h_arg_perm h_tail ih =>
      rename_i i τ expected bag rest args unused synthesized arg
      have h_arg_mem : arg ∈ bag :=
        (List.Perm.mem_iff h_arg_perm).1 (by simp)
      rcases pickAllOption_complete h_arg_mem h_match h_arg_perm with
        ⟨rest', h_pick, h_rest_perm⟩
      have h_tail_mem :
          RealizedArgs.mk args unused synthesized ∈
            enumerateRealizedArgsFrom (i + 1) expected rest' :=
        enumerateRealizedArgsFrom_of_perm h_rest_perm.symm ih
      have h_picks_ne : ¬pickAllOption τ bag = [] := by
        intro h_nil
        rw [h_nil] at h_pick
        simp at h_pick
      simp [enumerateRealizedArgsFrom, h_picks_ne]
      exact ⟨rest', h_pick, RealizedArgs.mk args unused synthesized, h_tail_mem, by simp⟩
  | option_omitted h_absent h_tail ih =>
      rename_i i τ expected bag args unused synthesized
      have h_picks : pickAllOption τ bag = [] :=
        pickAllOption_eq_nil_iff.2 h_absent
      simp [enumerateRealizedArgsFrom, h_picks]
      exact ⟨RealizedArgs.mk args unused synthesized, ih, by simp⟩
  | required h_not_option h_type h_arg_perm h_tail ih =>
      rename_i i τ expected bag rest args unused synthesized arg
      have h_arg_mem : arg ∈ bag :=
        (List.Perm.mem_iff h_arg_perm).1 (by simp)
      rcases pickAllExact_complete h_arg_mem h_type h_arg_perm with
        ⟨rest', h_pick, h_rest_perm⟩
      have h_tail_mem :
          RealizedArgs.mk args unused synthesized ∈
            enumerateRealizedArgsFrom (i + 1) expected rest' :=
        enumerateRealizedArgsFrom_of_perm h_rest_perm.symm ih
      cases τ <;> try contradiction
      all_goals
        simp [enumerateRealizedArgsFrom]
        exact ⟨rest', h_pick, RealizedArgs.mk args unused synthesized, h_tail_mem, by simp⟩

end RealizedArgsSelectionFrom

def enumerateAdmissible (Γ : Context) (e : Expr) : List RealizedCall :=
  let ops := filterOps e
  let bag_args := filterNonOps e
  match ops with
  | [Term.op name] =>
      match Γ name with
      | some (Ty.arrow τs_expected _) =>
          (enumerateRealizedArgs τs_expected bag_args).map
            (fun ra =>
              { opName := name, realizedArgs := ra })
      | _ => []
  | _ => []

def candidateValues (evalOp : EvalOpEngine) (Γ : Context) (e : Expr) : List Term :=
  (enumerateAdmissible Γ e).filterMap fun rc =>
    evalOp (realizedEvalName rc) (realizedEvalArgs rc)

/-- Relational realized-call admissibility. -/
inductive Admissible (Γ : Context) (e : Expr) : RealizedCall → Prop where
  | realized {name : String} {τs_expected : List Ty} {τ_out : Ty}
      {args : List Term} {unused : Multiset Term}
      {synthesized : List SynthesizedArg} :
      Γ name = some (Ty.arrow τs_expected τ_out) →
      filterOps e = [Term.op name] →
      RealizedArgsSelection τs_expected (filterNonOps e) args unused synthesized →
      Admissible Γ e
        { opName := name, realizedArgs := ⟨args, unused, synthesized⟩ }

theorem enumerate_admissible_iff {Γ : Context} {e : Expr} {rc : RealizedCall} :
    rc ∈ enumerateAdmissible Γ e ↔ Admissible Γ e rc := by
  constructor
  · intro h_mem
    unfold enumerateAdmissible enumerateRealizedArgs at h_mem
    cases h_ops : filterOps e with
    | nil =>
        simp [h_ops] at h_mem
    | cons op opsTail =>
        cases opsTail with
        | cons op₂ rest =>
            simp [h_ops] at h_mem
        | nil =>
            cases op <;> simp [h_ops] at h_mem
            case op name =>
              cases h_ctx : Γ name with
              | none =>
                  simp [h_ctx] at h_mem
              | some ty =>
                cases ty <;> simp [h_ctx] at h_mem
                case arrow τs_expected τ_out =>
                    rcases h_mem with ⟨ra, h_args, h_eq⟩
                    cases h_eq
                    exact Admissible.realized h_ctx (by simp [h_ops])
                      (RealizedArgsSelectionFrom.sound h_args)
  · intro h_adm
    cases h_adm with
    | realized h_ctx h_ops h_args =>
        unfold enumerateAdmissible enumerateRealizedArgs
        simp [h_ops, h_ctx]
        simpa using RealizedArgsSelectionFrom.complete h_args

/-- The ambiguity type exposed by the semantic layer. -/
def Amb (Γ : Context) (e : Expr) : Type :=
  { rc : RealizedCall // Admissible Γ e rc }

/-- Semantic singleton admissibility, independent of raw enumeration order. -/
def UniqueAdmissible (Γ : Context) (e : Expr) (rc : RealizedCall) : Prop :=
  Admissible Γ e rc ∧ ∀ rc', Admissible Γ e rc' → rc' = rc

theorem enumerate_realized_synthesized_wf
    {Γ : Context} {e : Expr} {rc : RealizedCall} {τs : List Ty} {τ_out : Ty} :
    rc ∈ enumerateAdmissible Γ e →
    Γ rc.opName = some (Ty.arrow τs τ_out) →
    SynthesizedWellFormed τs rc.realizedArgs.synthesized := by
  intro h_mem h_ctx
  unfold enumerateAdmissible enumerateRealizedArgs at h_mem
  cases h_ops : filterOps e with
  | nil =>
      simp [h_ops] at h_mem
  | cons op opsTail =>
      cases opsTail with
      | cons op₂ rest =>
          simp [h_ops] at h_mem
      | nil =>
          cases op <;> simp [h_ops] at h_mem
          case op name =>
            cases h_ctx_enum : Γ name with
            | none =>
                simp [h_ctx_enum] at h_mem
            | some ty =>
                cases ty <;> simp [h_ctx_enum] at h_mem
                case arrow τs_expected τ_enum_out =>
                  rcases h_mem with ⟨ra, h_result, h_eq⟩
                  cases h_eq
                  have h_arrow :
                      Ty.arrow τs_expected τ_enum_out = Ty.arrow τs τ_out := by
                    have h_some :
                        some (Ty.arrow τs_expected τ_enum_out) =
                          some (Ty.arrow τs τ_out) := by
                      rw [← h_ctx_enum, h_ctx]
                    injection h_some
                  cases h_arrow
                  rcases enumerateRealizedArgsFrom_synth_index_range h_result with
                    ⟨h_bounds, h_nodup⟩
                  constructor
                  · intro x hx
                    simpa using (h_bounds x hx).2
                  · exact h_nodup

lemma admissible_synthesized_wf
    {Γ : Context} {e : Expr} {rc : RealizedCall} {τs : List Ty} {τ_out : Ty} :
    Admissible Γ e rc →
    Γ rc.opName = some (Ty.arrow τs τ_out) →
    SynthesizedWellFormed τs rc.realizedArgs.synthesized :=
  fun h_adm h_ctx => enumerate_realized_synthesized_wf
    (enumerate_admissible_iff.2 h_adm) h_ctx

namespace Admissible

theorem of_perm {Γ : Context} {e₁ e₂ : Expr} {rc : RealizedCall}
    (h_perm : e₁.Perm e₂) :
    Admissible Γ e₁ rc → Admissible Γ e₂ rc := by
  intro h_adm
  have h_ops_perm : (filterOps e₁).Perm (filterOps e₂) := h_perm.filter Term.isOp
  have h_non_perm : (filterNonOps e₁).Perm (filterNonOps e₂) :=
    h_perm.filter Term.isNonOp
  cases h_adm with
  | realized h_ctx h_ops h_args =>
      rename_i name τs_expected τ_out args unused synthesized
      have h_ops₂ : filterOps e₂ = [Term.op name] :=
        List.perm_singleton.mp (by simpa [h_ops] using h_ops_perm.symm)
      exact Admissible.realized h_ctx h_ops₂
        (RealizedArgsSelectionFrom.of_perm h_non_perm h_args)

theorem perm_iff {Γ : Context} {e₁ e₂ : Expr} {rc : RealizedCall}
    (h_perm : e₁.Perm e₂) :
    Admissible Γ e₁ rc ↔ Admissible Γ e₂ rc :=
  ⟨of_perm h_perm, of_perm h_perm.symm⟩

end Admissible

lemma termType_of_optionArgMatches {Γ : Context} {τ : Ty} {arg : Term} :
    optionArgMatches τ arg = true → TermType Γ arg (Ty.option τ) := by
  intro h
  simp [optionArgMatches] at h
  rcases h with h_none | h_type
  · subst arg
    exact TermType.t_none
  · exact termType_of_typeOf h_type

lemma noOps_of_optionArgMatches_ne_none {τ : Ty} {arg : Term} :
    optionArgMatches τ arg = true → arg ≠ Term.none → arg.noOps := by
  intro h_match h_ne
  simp [optionArgMatches] at h_match
  rcases h_match with h_none | h_type
  · exact False.elim (h_ne h_none)
  · exact Term.noOps_of_typeOf_some h_type

namespace RealizedArgsSelectionFrom

lemma forall₂
    {Γ : Context} {i : Nat} {expected : List Ty} {bag args : List Term}
    {unused : Multiset Term} {synthesized : List SynthesizedArg} :
    RealizedArgsSelectionFrom i expected bag args unused synthesized →
      List.Forall₂ (TermType Γ) args expected := by
  intro h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | option_supplied h_match _ _ ih =>
      exact List.Forall₂.cons (termType_of_optionArgMatches h_match) ih
  | option_omitted _ _ ih =>
      exact List.Forall₂.cons TermType.t_none ih
  | required _ h_type _ _ ih =>
      exact List.Forall₂.cons (termType_of_typeOf h_type) ih

lemma noOps_filter
    {i : Nat} {expected : List Ty} {bag args : List Term}
    {unused : Multiset Term} {synthesized : List SynthesizedArg} :
    RealizedArgsSelectionFrom i expected bag args unused synthesized →
      noOps (args.filter (fun t => t != Term.none)) := by
  intro h
  induction h with
  | nil =>
      simp [noOps]
  | @option_supplied i τ expected bag rest args unused synthesized arg h_match h_perm h_tail =>
      rename_i ih
      by_cases h_arg_none : arg = Term.none
      · subst arg
        simpa using ih
      · intro t ht
        simp [h_arg_none] at ht
        rcases ht with rfl | ht_tail
        · exact noOps_of_optionArgMatches_ne_none h_match h_arg_none
        · exact ih t (by simpa using ht_tail)
  | option_omitted _ _ ih =>
      simpa using ih
  | @required i τ expected bag rest args unused synthesized arg h_not_option h_type h_perm h_tail =>
      rename_i ih
      have h_arg_ne : arg ≠ Term.none := by
        intro h_eq
        subst arg
        simp [Term.typeOf] at h_type
      intro t ht
      simp [h_arg_ne] at ht
      rcases ht with rfl | ht_tail
      · exact Term.noOps_of_typeOf_some h_type
      · exact ih t (by simpa using ht_tail)

lemma executableTypes
    {i : Nat} {expected : List Ty} {bag args : List Term}
    {unused : Multiset Term} {synthesized : List SynthesizedArg} :
    RealizedArgsSelectionFrom i expected bag args unused synthesized →
      AllExecutableTypes args expected := by
  intro h
  induction h with
  | nil =>
      exact AllExecutableTypes.nil
  | @option_supplied i τ expected bag rest args unused synthesized arg h_match _ _ ih =>
      by_cases h_arg_none : arg = Term.none
      · subst arg
        exact AllExecutableTypes.none ih
      · have h_type : arg.typeOf = some (Ty.option τ) := by
          simp [optionArgMatches] at h_match
          rcases h_match with h_none | h_type
          · exact False.elim (h_arg_none h_none)
          · exact h_type
        exact AllExecutableTypes.cons h_type ih
  | option_omitted _ _ ih =>
      exact AllExecutableTypes.none ih
  | required _ h_type _ _ ih =>
      exact AllExecutableTypes.cons h_type ih

lemma filter_args_perm_filter_bag_of_unused_zero
    {i : Nat} {expected : List Ty} {bag args : List Term}
    {unused : Multiset Term} {synthesized : List SynthesizedArg} :
    RealizedArgsSelectionFrom i expected bag args unused synthesized →
    unused = 0 →
      (args.filter (fun t => t != Term.none)).Perm
        (bag.filter (fun t => t != Term.none)) := by
  intro h
  induction h with
  | @nil i bag =>
      intro h_unused
      have h_card : bag.length = 0 := by
        have h_card_ms := congrArg Multiset.card h_unused
        simpa using h_card_ms
      cases bag with
      | nil =>
          simp
      | cons head tail =>
          simp at h_card
  | @option_supplied i τ expected bag rest args unused synthesized arg h_match h_arg_perm h_tail ih =>
      intro h_unused
      have h_tail_perm := ih h_unused
      have h_filter_perm :
          ((arg :: rest).filter (fun t => t != Term.none)).Perm
            (bag.filter (fun t => t != Term.none)) :=
        h_arg_perm.filter (fun t => t != Term.none)
      by_cases h_arg_none : arg = Term.none
      · have h_rest_perm :
            (rest.filter (fun t => t != Term.none)).Perm
              (bag.filter (fun t => t != Term.none)) := by
          simpa [h_arg_none] using h_filter_perm
        simpa [h_arg_none] using h_tail_perm.trans h_rest_perm
      · have h_cons_perm :
            (arg :: rest.filter (fun t => t != Term.none)).Perm
              (bag.filter (fun t => t != Term.none)) := by
          simpa [h_arg_none] using h_filter_perm
        simpa [h_arg_none] using
          (List.Perm.cons arg h_tail_perm).trans h_cons_perm
  | option_omitted _ _ ih =>
      intro h_unused
      simpa using ih h_unused
  | @required i τ expected bag rest args unused synthesized arg h_not_option h_type h_arg_perm h_tail ih =>
      intro h_unused
      have h_arg_ne : arg ≠ Term.none := by
        intro h_eq
        subst arg
        simp [Term.typeOf] at h_type
      have h_tail_perm := ih h_unused
      have h_filter_perm :
          ((arg :: rest).filter (fun t => t != Term.none)).Perm
            (bag.filter (fun t => t != Term.none)) :=
        h_arg_perm.filter (fun t => t != Term.none)
      have h_cons_perm :
          (arg :: rest.filter (fun t => t != Term.none)).Perm
            (bag.filter (fun t => t != Term.none)) := by
        simpa [h_arg_ne] using h_filter_perm
      simpa [h_arg_ne] using
        (List.Perm.cons arg h_tail_perm).trans h_cons_perm

lemma eq_unused_synth_of_eq_args
    {i : Nat} {expected : List Ty} {bag args₁ args₂ : List Term}
    {unused₁ unused₂ : Multiset Term}
    {synthesized₁ synthesized₂ : List SynthesizedArg} :
    RealizedArgsSelectionFrom i expected bag args₁ unused₁ synthesized₁ →
    RealizedArgsSelectionFrom i expected bag args₂ unused₂ synthesized₂ →
    args₁ = args₂ →
      unused₁ = unused₂ ∧ synthesized₁ = synthesized₂ := by
  induction expected generalizing i bag args₁ args₂ unused₁ unused₂ synthesized₁ synthesized₂ with
  | nil =>
      intro h₁ h₂ h_args
      cases h₁
      cases h₂
      exact ⟨rfl, rfl⟩
  | cons τ expected ih =>
      cases τ with
      | option τ_inner =>
          intro h₁ h₂ h_args
          cases h₁ with
          | option_supplied h_match₁ h_perm₁ h_tail₁ =>
              cases h₂ with
              | option_supplied h_match₂ h_perm₂ h_tail₂ =>
                  cases h_args
                  have h_rest_perm :=
                    List.Perm.cons_inv (h_perm₁.trans h_perm₂.symm)
                  exact ih h_tail₁
                    (RealizedArgsSelectionFrom.of_perm h_rest_perm.symm h_tail₂) rfl
              | option_omitted h_absent₂ h_tail₂ =>
                  cases h_args
                  have h_arg_mem : Term.none ∈ bag :=
                    (List.Perm.mem_iff h_perm₁).1 (by simp)
                  have h_false := h_absent₂ Term.none h_arg_mem
                  simp [optionArgMatches] at h_false
              | required h_not_option₂ _ _ _ =>
                  contradiction
          | option_omitted h_absent₁ h_tail₁ =>
              cases h₂ with
              | option_supplied h_match₂ h_perm₂ h_tail₂ =>
                  cases h_args
                  have h_arg_mem : Term.none ∈ bag :=
                    (List.Perm.mem_iff h_perm₂).1 (by simp)
                  have h_false := h_absent₁ Term.none h_arg_mem
                  simp [optionArgMatches] at h_false
              | option_omitted h_absent₂ h_tail₂ =>
                  cases h_args
                  rcases ih h_tail₁ h_tail₂ rfl with ⟨h_unused, h_synth⟩
                  exact ⟨h_unused, by simp [h_synth]⟩
              | required h_not_option₂ _ _ _ =>
                  contradiction
          | required h_not_option₁ _ _ _ =>
              contradiction
      | _ =>
          intro h₁ h₂ h_args
          cases h₁ with
          | required h_not_option₁ h_type₁ h_perm₁ h_tail₁ =>
              cases h₂ with
              | required h_not_option₂ h_type₂ h_perm₂ h_tail₂ =>
                  cases h_args
                  have h_rest_perm :=
                    List.Perm.cons_inv (h_perm₁.trans h_perm₂.symm)
                  exact ih h_tail₁
                    (RealizedArgsSelectionFrom.of_perm h_rest_perm.symm h_tail₂) rfl

end RealizedArgsSelectionFrom

lemma typeOf_of_allExecutableTypes_mem {args : List Term} {τs : List Ty}
    {t : Term} :
    AllExecutableTypes args τs →
    t ∈ args →
    t ≠ Term.none →
    ∃ τ, τ ∈ τs ∧ t.typeOf = some τ := by
  intro h_args
  induction h_args with
  | nil =>
      intro h_mem _
      simp at h_mem
  | none h_tail ih =>
      intro h_mem h_ne
      simp at h_mem
      rcases h_mem with rfl | h_tail_mem
      · exact False.elim (h_ne rfl)
      · rcases ih h_tail_mem h_ne with ⟨τ, hτ_mem, h_type⟩
        exact ⟨τ, by simp [hτ_mem], h_type⟩
  | cons h_type h_tail ih =>
      intro h_mem h_ne
      simp at h_mem
      rcases h_mem with rfl | h_tail_mem
      · exact ⟨_, by simp, h_type⟩
      · rcases ih h_tail_mem h_ne with ⟨τ, hτ_mem, h_type⟩
        exact ⟨τ, by simp [hτ_mem], h_type⟩

lemma executable_args_eq_of_nodup_filter_perm
    {args₁ args₂ : List Term} {τs : List Ty}
    (h_nodup : τs.Nodup)
    (h_args₁ : AllExecutableTypes args₁ τs)
    (h_args₂ : AllExecutableTypes args₂ τs)
    (h_perm :
      (args₁.filter (fun t => t != Term.none)).Perm
        (args₂.filter (fun t => t != Term.none))) :
    args₁ = args₂ := by
  induction h_args₁ generalizing args₂ with
  | nil =>
      cases h_args₂
      rfl
  | none h_tail₁ ih =>
      rename_i τ tail₁ τs
      cases h_args₂ with
      | none h_tail₂ =>
          rename_i τ tail₂
          simp at h_nodup
          rcases h_nodup with ⟨_, h_tail_nodup⟩
          have h_tail_perm :
              (tail₁.filter (fun t => t != Term.none)).Perm
                (tail₂.filter (fun t => t != Term.none)) := by
            simpa using h_perm
          exact congrArg (List.cons Term.none)
            (ih h_tail_nodup h_tail₂ h_tail_perm)
      | cons h_head₂_type h_tail₂ =>
          rename_i head₂ tail₂
          simp at h_nodup
          rcases h_nodup with ⟨hτ_not_mem, _⟩
          have h_head₂_ne : head₂ ≠ Term.none := by
            intro h_eq
            subst head₂
            simp [Term.typeOf] at h_head₂_type
          have h_head₂_mem_filter :
              head₂ ∈ (head₂ :: tail₂).filter (fun t => t != Term.none) := by
            simp [h_head₂_ne]
          have h_head₂_mem_left :
              head₂ ∈ (tail₁.filter (fun t => t != Term.none)) := by
            have h_mem :=
              (List.Perm.mem_iff h_perm).2 h_head₂_mem_filter
            simpa using h_mem
          rcases typeOf_of_allExecutableTypes_mem h_tail₁
              (List.mem_of_mem_filter h_head₂_mem_left) h_head₂_ne with
            ⟨υ, hυ_mem, hυ_type⟩
          have h_eq_ty : υ = Ty.option τ := by
            have h_some : some υ = some (Ty.option τ) := by
              rw [← hυ_type, h_head₂_type]
            injection h_some
          exact False.elim (hτ_not_mem (by simpa [h_eq_ty] using hυ_mem))
  | cons h_head₁_type h_tail₁ ih =>
      rename_i head₁ tail₁ τ τs
      have h_head₁_none : head₁ ≠ Term.none := by
        intro h_eq
        subst head₁
        simp [Term.typeOf] at h_head₁_type
      cases h_args₂ with
      | none h_tail₂ =>
          rename_i τ₂ tail₂
          simp at h_nodup
          rcases h_nodup with ⟨hτ_not_mem, _⟩
          have h_head₁_mem_filter :
              head₁ ∈ (head₁ :: tail₁).filter (fun t => t != Term.none) := by
            simp [h_head₁_none]
          have h_head₁_mem_right :
              head₁ ∈ (tail₂.filter (fun t => t != Term.none)) := by
            have h_mem :=
              (List.Perm.mem_iff h_perm).1 h_head₁_mem_filter
            simpa using h_mem
          rcases typeOf_of_allExecutableTypes_mem h_tail₂
              (List.mem_of_mem_filter h_head₁_mem_right) h_head₁_none with
            ⟨υ, hυ_mem, hυ_type⟩
          have h_eq_ty : υ = Ty.option τ₂ := by
            have h_some : some υ = head₁.typeOf := by
              rw [hυ_type]
            rw [h_head₁_type] at h_some
            injection h_some
          exact False.elim (hτ_not_mem (by simpa [h_eq_ty] using hυ_mem))
      | cons h_head₂ h_tail₂ =>
          rename_i head₂ tail₂
          simp at h_nodup
          rcases h_nodup with ⟨hτ_not_mem, h_tail_nodup⟩
          have h_head₂_ne : head₂ ≠ Term.none := by
            intro h_eq
            subst head₂
            simp [Term.typeOf] at h_head₂
          have h_head₁_mem_filter :
              head₁ ∈ (head₁ :: tail₁).filter (fun t => t != Term.none) := by
            simp [h_head₁_none]
          have h_head_eq : head₁ = head₂ := by
            have h_head₁_mem_right :
                head₁ ∈ (head₂ :: tail₂).filter (fun t => t != Term.none) :=
              (List.Perm.mem_iff h_perm).1 h_head₁_mem_filter
            simp [h_head₂_ne] at h_head₁_mem_right
            rcases h_head₁_mem_right with h_eq | h_tail_mem
            · exact h_eq
            · rcases typeOf_of_allExecutableTypes_mem h_tail₂
                h_tail_mem.1 h_head₁_none with
              ⟨υ, hυ_mem, hυ_type⟩
              have h_eq_ty : υ = τ := by
                have h_some : some υ = some τ := by
                  rw [← hυ_type, h_head₁_type]
                injection h_some
              exact False.elim (hτ_not_mem (by simpa [h_eq_ty] using hυ_mem))
          subst head₂
          have h_tail_perm :
              (tail₁.filter (fun t => t != Term.none)).Perm
                (tail₂.filter (fun t => t != Term.none)) := by
            have h_cons_perm :
                (head₁ :: tail₁.filter (fun t => t != Term.none)).Perm
                  (head₁ :: tail₂.filter (fun t => t != Term.none)) := by
              simpa [h_head₁_none, h_head₂_ne] using h_perm
            exact List.Perm.cons_inv h_cons_perm
          exact congrArg (List.cons head₁)
            (ih h_tail_nodup h_tail₂ h_tail_perm)

theorem distinct_parameter_types_unique
    {Γ : Context} {e : Expr} {rc : RealizedCall} :
    HasDistinctParameterTypes Γ rc.opName →
    Admissible Γ e rc →
    (∀ rc', Admissible Γ e rc' →
      (rc.realizedArgs.args.filter (fun t => t != Term.none)).Perm
        (rc'.realizedArgs.args.filter (fun t => t != Term.none))) →
    UniqueAdmissible Γ e rc := by
  intro h_distinct h_adm h_same_filters
  constructor
  · exact h_adm
  · intro rc' h_adm'
    cases h_adm with
    | realized h_ctx h_ops h_sel =>
        rename_i name τs_expected τ_out args unused synthesized
        rcases h_distinct with ⟨τs_distinct, τ_out_distinct,
          h_ctx_distinct, h_nodup_distinct⟩
        have h_distinct_arrow :
            Ty.arrow τs_distinct τ_out_distinct =
              Ty.arrow τs_expected τ_out := by
          have h_some :
              some (Ty.arrow τs_distinct τ_out_distinct) =
                some (Ty.arrow τs_expected τ_out) := by
            rw [← h_ctx_distinct, h_ctx]
          injection h_some
        cases h_distinct_arrow
        cases h_adm' with
        | realized h_ctx' h_ops' h_sel' =>
            rename_i name' τs_expected' τ_out' args' unused' synthesized'
            have h_name : name' = name := by
              rw [h_ops] at h_ops'
              injection h_ops' with h_op_eq
              injection h_op_eq with h_name_eq
              exact h_name_eq.symm
            subst name'
            have h_arrow :
                Ty.arrow τs_expected' τ_out' =
                  Ty.arrow τs_expected τ_out := by
              have h_some :
                  some (Ty.arrow τs_expected' τ_out') =
                    some (Ty.arrow τs_expected τ_out) := by
                rw [← h_ctx', h_ctx]
              injection h_some
            cases h_arrow
            have h_args : AllExecutableTypes args τs_expected :=
              RealizedArgsSelectionFrom.executableTypes h_sel
            have h_args' : AllExecutableTypes args' τs_expected :=
              RealizedArgsSelectionFrom.executableTypes h_sel'
            have h_filter_perm :
                (args.filter (fun t => t != Term.none)).Perm
                  (args'.filter (fun t => t != Term.none)) := by
              simpa using h_same_filters
                { opName := name,
                  realizedArgs := ⟨args', unused', synthesized'⟩ }
                (Admissible.realized h_ctx' h_ops' h_sel')
            have h_args_eq : args = args' :=
              executable_args_eq_of_nodup_filter_perm
                h_nodup_distinct h_args h_args' h_filter_perm
            subst args'
            rcases RealizedArgsSelectionFrom.eq_unused_synth_of_eq_args h_sel h_sel' rfl with
              ⟨h_unused, h_synthesized⟩
            subst unused'
            subst synthesized'
            rfl

theorem exact_distinct_parameter_types_unique
    {Γ : Context} {e : Expr} {rc : RealizedCall} :
    HasDistinctParameterTypes Γ rc.opName →
    Admissible Γ e rc →
    (∀ rc', Admissible Γ e rc' → rc'.realizedArgs.unused = 0) →
    UniqueAdmissible Γ e rc := by
  intro h_distinct h_adm h_all_exact
  refine distinct_parameter_types_unique h_distinct h_adm ?_
  intro rc' h_adm'
  cases h_adm with
  | realized h_ctx h_ops h_sel =>
      rename_i name τs_expected τ_out args unused synthesized
      have h_rc_exact : unused = 0 := by
        simpa using h_all_exact
          { opName := name,
            realizedArgs := ⟨args, unused, synthesized⟩ }
          (Admissible.realized h_ctx h_ops h_sel)
      cases h_adm' with
      | realized h_ctx' h_ops' h_sel' =>
          rename_i name' τs_expected' τ_out' args' unused' synthesized'
          have h_rc'_exact : unused' = 0 := by
            simpa using h_all_exact
              { opName := name',
                realizedArgs := ⟨args', unused', synthesized'⟩ }
              (Admissible.realized h_ctx' h_ops' h_sel')
          have h_left :
              (args.filter (fun t => t != Term.none)).Perm
                ((filterNonOps e).filter (fun t => t != Term.none)) :=
            RealizedArgsSelectionFrom.filter_args_perm_filter_bag_of_unused_zero
              h_sel h_rc_exact
          have h_right :
              (args'.filter (fun t => t != Term.none)).Perm
                ((filterNonOps e).filter (fun t => t != Term.none)) :=
            RealizedArgsSelectionFrom.filter_args_perm_filter_bag_of_unused_zero
              h_sel' h_rc'_exact
          exact h_left.trans h_right.symm

lemma mem_eraseDups_iff_of_lawful
    {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {x : α} :
    x ∈ xs.eraseDups ↔ x ∈ xs := by
  induction xs with
  | nil =>
      simp
  | cons a as ih =>
      rw [List.eraseDups_cons]
      constructor
      · intro h
        simp at h ⊢
        rcases h with hxa | htail
        · exact Or.inl hxa
        · exact Or.inr htail.1
      · intro h
        simp at h ⊢
        rcases h with hxa | hxas
        · exact Or.inl hxa
        · by_cases hxa : x = a
          · exact Or.inl hxa
          · exact Or.inr ⟨hxas, hxa⟩

lemma eraseDups_eq_singleton_iff_mem_all_eq
    {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {c : α} :
    xs.eraseDups = [c] ↔ c ∈ xs ∧ ∀ y, y ∈ xs → y = c := by
  constructor
  · intro h
    constructor
    · exact mem_eraseDups_iff_of_lawful.1 (by rw [h]; simp)
    · intro y hy
      have hmem : y ∈ xs.eraseDups := mem_eraseDups_iff_of_lawful.2 hy
      rw [h] at hmem
      simpa using hmem
  · rintro ⟨hc, hall⟩
    cases xs with
    | nil =>
        simp at hc
    | cons a as =>
        have ha := hall a (List.Mem.head as)
        subst c
        have hfilter : (as.filter fun b => !b == a) = [] := by
          apply List.eq_nil_iff_forall_not_mem.2
          intro y hy
          simp at hy
          have hya := hall y (List.mem_cons_of_mem a hy.1)
          subst y
          simp at hy
        rw [List.eraseDups_cons, hfilter]
        simp

theorem unique_admissible_iff_dedup_singleton
    {Γ : Context} {e : Expr} {rc : RealizedCall} :
    UniqueAdmissible Γ e rc ↔
      (enumerateAdmissible Γ e).eraseDups = [rc] := by
  rw [eraseDups_eq_singleton_iff_mem_all_eq]
  exact ⟨fun h => ⟨enumerate_admissible_iff.2 h.1,
      fun rc' hm => h.2 rc' (enumerate_admissible_iff.1 hm)⟩,
    fun ⟨hm, ha⟩ =>
      ⟨enumerate_admissible_iff.1 hm,
        fun rc' had => ha rc' (enumerate_admissible_iff.2 had)⟩⟩

inductive AmbCardinality where
  | zero
  | one
  | many
deriving Repr, DecidableEq

/-- Semantic ambiguity-space cardinality classification. -/
noncomputable def AmbCard (Γ : Context) (e : Expr) : AmbCardinality := by
  classical
  exact
    if h0 : ∀ rc, ¬Admissible Γ e rc then
      AmbCardinality.zero
    else if h1 : ∃ rc, UniqueAdmissible Γ e rc then
      AmbCardinality.one
    else
      AmbCardinality.many

lemma eraseDups_eq_nil_iff
    {α : Type} [BEq α] [LawfulBEq α] {xs : List α} :
    xs.eraseDups = [] ↔ xs = [] := by
  rw [List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  exact ⟨fun h x hx => h x (mem_eraseDups_iff_of_lawful.2 hx),
    fun h x hx => h x (mem_eraseDups_iff_of_lawful.1 hx)⟩

theorem AmbCard_zero_iff_enumerate_nil
    {Γ : Context} {e : Expr} :
    AmbCard Γ e = AmbCardinality.zero ↔
      enumerateAdmissible Γ e = [] := by
  constructor
  · intro h
    unfold AmbCard at h
    by_cases h0 : ∀ rc, ¬Admissible Γ e rc
    · exact List.eq_nil_iff_forall_not_mem.2
        (fun rc h_mem => h0 rc (enumerate_admissible_iff.1 h_mem))
    · by_cases h1 : ∃ rc, UniqueAdmissible Γ e rc
      · exfalso
        simp [h0, h1] at h
      · exfalso
        simp [h0, h1] at h
  · intro h_enum
    unfold AmbCard
    have h0 : ∀ rc, ¬Admissible Γ e rc := by
      intro rc h_adm
      have h_mem := enumerate_admissible_iff.2 h_adm
      rw [h_enum] at h_mem
      simp at h_mem
    simp [h0]

theorem AmbCard_one_iff_exists_singleton
    {Γ : Context} {e : Expr} :
    AmbCard Γ e = AmbCardinality.one ↔
      ∃ rc, (enumerateAdmissible Γ e).eraseDups = [rc] := by
  constructor
  · intro h
    unfold AmbCard at h
    by_cases h0 : ∀ rc, ¬Admissible Γ e rc
    · exfalso
      simp [h0] at h
    · by_cases h1 : ∃ rc, UniqueAdmissible Γ e rc
      · rcases h1 with ⟨rc, h_unique⟩
        exact ⟨rc, (unique_admissible_iff_dedup_singleton.1
          h_unique)⟩
      · exfalso
        simp [h0, h1] at h
  · rintro ⟨rc, h_enum⟩
    have h_unique : UniqueAdmissible Γ e rc :=
      unique_admissible_iff_dedup_singleton.2 h_enum
    unfold AmbCard
    have h0 : ¬∀ rc, ¬Admissible Γ e rc := by
      intro h_none
      exact h_none rc h_unique.1
    have h1 : ∃ rc, UniqueAdmissible Γ e rc :=
      ⟨rc, h_unique⟩
    simp [h0, h1]

theorem AmbCard_many_iff_exists_cons_cons
    {Γ : Context} {e : Expr} :
    AmbCard Γ e = AmbCardinality.many ↔
      ∃ rc₁ rc₂ rest,
        (enumerateAdmissible Γ e).eraseDups = rc₁ :: rc₂ :: rest := by
  constructor
  · intro h_many
    cases h_dedup : (enumerateAdmissible Γ e).eraseDups with
    | nil =>
        have h_enum : enumerateAdmissible Γ e = [] :=
          eraseDups_eq_nil_iff.1 h_dedup
        have h_zero := (AmbCard_zero_iff_enumerate_nil).2 h_enum
        simp [h_many] at h_zero
    | cons rc rest =>
        cases rest with
        | nil =>
            have h_one := (AmbCard_one_iff_exists_singleton).2
              ⟨rc, h_dedup⟩
            simp [h_many] at h_one
        | cons rc₂ rest =>
            exact ⟨rc, rc₂, rest, rfl⟩
  · rintro ⟨rc₁, rc₂, rest, h_dedup⟩
    cases h_card : AmbCard Γ e with
    | zero =>
        have h_enum := (AmbCard_zero_iff_enumerate_nil).1 h_card
        rw [h_enum] at h_dedup
        simp at h_dedup
    | one =>
        rcases (AmbCard_one_iff_exists_singleton).1 h_card with ⟨rc, h_one⟩
        rw [h_one] at h_dedup
        simp at h_dedup
    | many =>
        rfl

theorem many_cardinality_has_two_realized_branches
    {Γ : Context} {e : Expr}
    (h_many : AmbCard Γ e = AmbCardinality.many) :
    ∃ rc₁ rc₂ rest,
      rc₁ ≠ rc₂ ∧
      (enumerateAdmissible Γ e).eraseDups = rc₁ :: rc₂ :: rest := by
  rcases (AmbCard_many_iff_exists_cons_cons).1 h_many with
    ⟨rc₁, rc₂, rest, h_enum⟩
  have h_mem₁ : rc₁ ∈ enumerateAdmissible Γ e :=
    mem_eraseDups_iff_of_lawful.1 (by rw [h_enum]; simp)
  have h_mem₂ : rc₂ ∈ enumerateAdmissible Γ e :=
    mem_eraseDups_iff_of_lawful.1 (by rw [h_enum]; simp)
  have h_ne : rc₁ ≠ rc₂ := by
    cases h_src : enumerateAdmissible Γ e with
    | nil =>
        rw [h_src] at h_enum
        simp at h_enum
    | cons x xs =>
        rw [h_src, List.eraseDups_cons] at h_enum
        injection h_enum with h_rc₁ h_tail
        subst rc₁
        intro h_eq
        subst rc₂
        have h_mem_tail : x ∈ (xs.filter fun y => !y == x).eraseDups := by
          rw [h_tail]
          simp
        have h_mem_filter : x ∈ xs.filter (fun y => !y == x) :=
          mem_eraseDups_iff_of_lawful.1 h_mem_tail
        simp at h_mem_filter
  aesop

/-- An ambiguity class collapses when every admissible branch evaluates to the same value. -/
def CollapsesTo (evalOp : EvalOpEngine) (Γ : Context) (e : Expr) (v : Term) : Prop :=
  Nonempty (Amb Γ e) ∧
    ∀ c : Amb Γ e, evalOp (realizedEvalName c.val) (realizedEvalArgs c.val) = some v

theorem CollapsesTo.det {evalOp : EvalOpEngine} {Γ : Context} {e : Expr}
    {v₁ v₂ : Term} :
    CollapsesTo evalOp Γ e v₁ →
    CollapsesTo evalOp Γ e v₂ →
    v₁ = v₂ := by
  intro h_col₁ h_col₂
  rcases h_col₁.1 with ⟨c⟩
  have := h_col₁.2 c; have := h_col₂.2 c
  simp_all

/-- All admissible calls in one ambiguity class come from the same operator. -/
lemma Admissible.same_opName
    {Γ : Context} {e : Expr} {rc₁ rc₂ : RealizedCall}
    (h₁ : Admissible Γ e rc₁) (h₂ : Admissible Γ e rc₂) :
    rc₁.opName = rc₂.opName := by
  cases h₁ with
  | realized h_ctx₁ h_ops₁ h_args₁ =>
      cases h₂ with
      | realized h_ctx₂ h_ops₂ h_args₂ =>
          simp
          simpa [h_ops₁] using h_ops₂

namespace Amb

/-- All branches exposed as `Amb Γ e` share their realized operator name. -/
lemma same_opName {Γ : Context} {e : Expr} (c₁ c₂ : Amb Γ e) :
    realizedEvalName c₁.val = realizedEvalName c₂.val :=
  Admissible.same_opName c₁.property c₂.property

end Amb

/-- Branch-invariance for one explicitly selected operator. -/
def EvalOpInvariant
    (evalOp : EvalOpEngine) (opName : String) (Γ : Context) (e : Expr) : Prop :=
  ∀ c₁ c₂ : Amb Γ e,
    evalOp opName (realizedEvalArgs c₁.val) =
      evalOp opName (realizedEvalArgs c₂.val)

def observational_collapse
    {evalOp : EvalOpEngine} {Γ : Context} {e : Expr} {v : Term}
    (h : CollapsesTo evalOp Γ e v) :
    ∀ c : Amb Γ e, evalOp (realizedEvalName c.val) (realizedEvalArgs c.val) = some v := h.2

def observational_collapse_eq
    {evalOp : EvalOpEngine} {Γ : Context} {e : Expr} {v : Term}
    (h : CollapsesTo evalOp Γ e v) :
    ∀ c₁ c₂ : Amb Γ e,
      evalOp (realizedEvalName c₁.val) (realizedEvalArgs c₁.val) =
        evalOp (realizedEvalName c₂.val) (realizedEvalArgs c₂.val) :=
  fun c₁ c₂ => by rw [h.2 c₁, h.2 c₂]

def unique_admissible_of_all_admissible_eq
    {Γ : Context} {e : Expr} {rc : RealizedCall}
    (h_adm : Admissible Γ e rc)
    (h_all : ∀ rc', Admissible Γ e rc' → rc' = rc) :
    UniqueAdmissible Γ e rc :=
  ⟨h_adm, h_all⟩

def all_admissible_eval_eq_implies_collapse
    {evalOp : EvalOpEngine} {opName : String} {Γ : Context} {e : Expr}
    {ref : Amb Γ e} {v : Term}
    (h_ref_name : realizedEvalName ref.val = opName)
    (h_inv : EvalOpInvariant evalOp opName Γ e)
    (h_eval : evalOp opName (realizedEvalArgs ref.val) = some v) :
    CollapsesTo evalOp Γ e v := by
  constructor
  · exact ⟨ref⟩
  · intro c
    have h_c_name : realizedEvalName c.val = opName := by
      rw [Amb.same_opName c ref, h_ref_name]
    rw [h_c_name, h_inv c ref, h_eval]

/-- Theorem-level certificates for constructing collapsed evaluations. -/
inductive CollapseCert
    (evalOp : EvalOpEngine) (Γ : Context) (e : Expr) (v : Term) : Prop where
  | unique {rc : RealizedCall} :
      UniqueAdmissible Γ e rc →
      evalOp (realizedEvalName rc) (realizedEvalArgs rc) = some v →
      CollapseCert evalOp Γ e v
  | finiteBranchCollapse {rcs : List RealizedCall} :
      (enumerateAdmissible Γ e).eraseDups = rcs →
      rcs ≠ [] →
      (∀ rc, rc ∈ rcs →
        evalOp (realizedEvalName rc) (realizedEvalArgs rc) = some v) →
      CollapseCert evalOp Γ e v
  | invariantCollapse {opName : String} {ref : Amb Γ e} :
      realizedEvalName ref.val = opName →
      EvalOpInvariant evalOp opName Γ e →
      evalOp opName (realizedEvalArgs ref.val) = some v →
      CollapseCert evalOp Γ e v

/-
The results below are used either directly or indirectly by the automated checker tactic defined in `checker.lean`
-/

theorem CollapseCert.sound
    {evalOp : EvalOpEngine} {Γ : Context} {e : Expr} {v : Term} :
    CollapseCert evalOp Γ e v →
    CollapsesTo evalOp Γ e v := by
  intro cert
  cases cert with
  | unique h_unique h_eval =>
      constructor
      · exact ⟨⟨_, h_unique.1⟩⟩
      · intro c
        have h_eq := h_unique.2 c.val c.property
        subst h_eq
        exact h_eval
  | finiteBranchCollapse h_enum h_ne h_all =>
      rename_i rcs
      constructor
      · cases h_rcs : rcs with
        | nil =>
            exact False.elim (h_ne h_rcs)
        | cons rc rest =>
            have h_mem_dedup : rc ∈ (enumerateAdmissible Γ e).eraseDups := by
              rw [h_enum, h_rcs]
              simp
            exact ⟨⟨rc, enumerate_admissible_iff.1
              (mem_eraseDups_iff_of_lawful.1 h_mem_dedup)⟩⟩
      · intro c
        have h_mem_enum : c.val ∈ enumerateAdmissible Γ e :=
          enumerate_admissible_iff.2 c.property
        have h_mem_dedup : c.val ∈ (enumerateAdmissible Γ e).eraseDups :=
          mem_eraseDups_iff_of_lawful.2 h_mem_enum
        have h_mem_rcs : c.val ∈ rcs := by
          rwa [h_enum] at h_mem_dedup
        exact h_all c.val h_mem_rcs
  | invariantCollapse h_ref_name h_inv h_eval =>
      exact all_admissible_eval_eq_implies_collapse h_ref_name h_inv h_eval

lemma eval_by_cert
    {evalOp : EvalOpEngine} {Γ : Context} {e : Expr} {v : Term}
    (cert : CollapseCert evalOp Γ e v) :
    CollapsesTo evalOp Γ e v :=
  CollapseCert.sound cert

lemma finite_branch_collapse_cert
    {evalOp : EvalOpEngine} {Γ : Context} {e : Expr} {v : Term}
    (h_ne : Nonempty (Amb Γ e))
    (h_all : ∀ c : Amb Γ e,
      evalOp (realizedEvalName c.val) (realizedEvalArgs c.val) = some v) :
    CollapseCert evalOp Γ e v := by
  refine CollapseCert.finiteBranchCollapse
    (rcs := (enumerateAdmissible Γ e).eraseDups) rfl ?_ ?_
  · intro h_nil
    rcases h_ne with ⟨c⟩
    have h_mem : c.val ∈ (enumerateAdmissible Γ e).eraseDups :=
      mem_eraseDups_iff_of_lawful.2 (enumerate_admissible_iff.2 c.property)
    rw [h_nil] at h_mem
    simp at h_mem
  · intro rc h_mem
    have h_adm : Admissible Γ e rc :=
      enumerate_admissible_iff.1 (mem_eraseDups_iff_of_lawful.1 h_mem)
    exact h_all ⟨rc, h_adm⟩

lemma invariant_collapse_cert
    {evalOp : EvalOpEngine} {opName : String} {Γ : Context} {e : Expr}
    {ref : Amb Γ e} {v : Term}
    (h_ref_name : realizedEvalName ref.val = opName)
    (h_inv : EvalOpInvariant evalOp opName Γ e)
    (h_eval : evalOp opName (realizedEvalArgs ref.val) = some v) :
    CollapseCert evalOp Γ e v :=
  CollapseCert.invariantCollapse h_ref_name h_inv h_eval

lemma finite_enumeration_collapse_cert
    {evalOp : EvalOpEngine} {Γ : Context} {e : Expr} {v : Term}
  (h_ne : ∃ rc, rc ∈ enumerateAdmissible Γ e)
  (h_all :
      ∀ rc, rc ∈ enumerateAdmissible Γ e →
        evalOp (realizedEvalName rc) (realizedEvalArgs rc) = some v) :
    CollapseCert evalOp Γ e v := by
  refine CollapseCert.finiteBranchCollapse
    (rcs := (enumerateAdmissible Γ e).eraseDups) rfl ?_ ?_
  · rcases h_ne with ⟨c, h_mem⟩
    intro h_nil
    have h_mem_dedup : c ∈ (enumerateAdmissible Γ e).eraseDups :=
      mem_eraseDups_iff_of_lawful.2 h_mem
    rw [h_nil] at h_mem_dedup
    simp at h_mem_dedup
  · intro rc h_mem
    exact h_all rc (mem_eraseDups_iff_of_lawful.1 h_mem)
