/-
Examples for testing `discharge_collapse_cert`.
-/

import checker

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

noncomputable section

namespace CollapseCertExamples

/-! ## 1. Singleton admissibility: distinct parameter types -/

def Γ_averageLatency : Context
  | "averageLatency" => some (Ty.arrow [Ty.str, Ty.nat] Ty.nat)
  | _ => none

def eval_averageLatency : EvalOpEngine
  | "averageLatency", [Term.str _, Term.nat n] => some (Term.nat n)
  | _, _ => none

example :
    CollapseCert eval_averageLatency Γ_averageLatency
      [Term.op "averageLatency", Term.nat 10, Term.str "/api"]
      (Term.nat 10) := by discharge_collapse_cert

/-! ## 2. Definitional collapse: same same-typed arguments -/

def Γ_check_same : Context
  | "checkExpect" => some (Ty.arrow [Ty.nat, Ty.nat] Ty.str)
  | _ => none

def eval_check_same : EvalOpEngine
  | "checkExpect", [Term.nat x, Term.nat y] =>
      if x = y then some (Term.str "pass") else some (Term.str "fail")
  | _, _ => none

example :
    CollapseCert eval_check_same Γ_check_same
      [Term.op "checkExpect", Term.nat 5, Term.nat 5]
      (Term.str "pass") := by
  discharge_collapse_cert

/-! ## 3. Expected failure: noncommutative same-typed arguments -/

/-
This should fail: both orderings are admissible, but the intended target value
is not produced by all branches.

Uncomment when testing failure diagnostics.
-/
-- example :
--     CollapseCert eval_check_same Γ_check_same
--       [Term.op "checkExpect", Term.nat 5, Term.nat 6]
--       (Term.str "fail") := by
--   discharge_collapse_cert

/-! ## 4. Nominal refinement: singleton admissibility via role type -/

def Γ_nominal_check : Context
  | "checkExpect" =>
      some (Ty.arrow [Ty.nominal "Expected" Ty.nat, Ty.nat] Ty.str)
  | _ => none

def eval_nominal_check : EvalOpEngine
  | "checkExpect", [Term.wrap "Expected" (Term.nat x), Term.nat y] =>
      if x = y then some (Term.str "pass") else some (Term.str "fail")
  | _, _ => none

example :
    CollapseCert eval_nominal_check Γ_nominal_check
      [Term.op "checkExpect", Term.nat 7, Term.wrap "Expected" (Term.nat 6)]
      (Term.str "fail") := by
  discharge_collapse_cert

/-! ## 5. Concrete commutative operator: observational collapse by evaluation -/

def Γ_add : Context
  | "add" => some (Ty.arrow [Ty.nat, Ty.nat] Ty.nat)
  | _ => none

def eval_add : EvalOpEngine
  | "add", [Term.nat x, Term.nat y] => some (Term.nat (x + y))
  | _, _ => none

example :
    CollapseCert eval_add Γ_add
      [Term.op "add", Term.nat 2, Term.nat 3]
      (Term.nat 5) := by
  discharge_collapse_cert

example
    (h_inv :
      EvalOpInvariant eval_add "add" Γ_add
        [Term.op "add", Term.nat 2, Term.nat 3]) :
    CollapseCert eval_add Γ_add
      [Term.op "add", Term.nat 2, Term.nat 3]
      (Term.nat 5) := by
  let ref :
      Amb Γ_add [Term.op "add", Term.nat 2, Term.nat 3] :=
    ⟨{ opName := "add",
       realizedArgs := { args := [Term.nat 2, Term.nat 3], unused := 0, synthesized := [] } },
      by
        refine Admissible.realized (name := "add")
          (τs_expected := [Ty.nat, Ty.nat]) (τ_out := Ty.nat)
          (args := [Term.nat 2, Term.nat 3]) (unused := 0)
          (synthesized := []) ?_ ?_ ?_
        · rfl
        · rfl
        · unfold RealizedArgsSelection
          refine RealizedArgsSelectionFrom.required (arg := Term.nat 2)
            (rest := [Term.nat 3]) ?_ ?_ ?_ ?_
          · simp
          · rfl
          · exact List.Perm.refl _
          · refine RealizedArgsSelectionFrom.required (arg := Term.nat 3)
              (rest := []) ?_ ?_ ?_ ?_
            · simp
            · rfl
            · exact List.Perm.refl _
            · exact RealizedArgsSelectionFrom.nil⟩
  exact invariant_collapse_cert (opName := "add") (ref := ref) rfl h_inv rfl

/-! ## 6. Symbolic commutative operator: may require arithmetic rewriting -/

example (x y : Nat) :
    CollapseCert eval_add Γ_add
      [Term.op "add", Term.nat x, Term.nat y]
      (Term.nat (x + y)) := by
  discharge_collapse_cert

/-! ## 7. Optional synthesis: omitted option should synthesize `none` -/

def Γ_optional_limit : Context
  | "limit" => some (Ty.arrow [Ty.nat, Ty.option Ty.nat] Ty.nat)
  | _ => none

def eval_optional_limit : EvalOpEngine
  | "limit", [Term.nat n, Term.none] => some (Term.nat n)
  | "limit", [Term.nat n, Term.some (Term.nat m)] => some (Term.nat (n + m))
  | _, _ => none

example :
    CollapseCert eval_optional_limit Γ_optional_limit
      [Term.op "limit", Term.nat 10]
      (Term.nat 10) := by
  discharge_collapse_cert

/-! ## 8. Optional synthesis: two omitted options synthesize `none` -/

def Γ_two_options : Context
  | "choose" => some (Ty.arrow [Ty.option Ty.nat, Ty.option Ty.nat] Ty.nat)
  | _ => none

def eval_two_options : EvalOpEngine
  | "choose", [Term.none, Term.none] => some (Term.nat 0)
  | "choose", [Term.some (Term.nat x), Term.none] => some (Term.nat x)
  | "choose", [Term.none, Term.some (Term.nat y)] => some (Term.nat y)
  | "choose", [Term.some (Term.nat x), Term.some (Term.nat y)] =>
      some (Term.nat (x + y))
  | _, _ => none

example :
    CollapseCert eval_two_options Γ_two_options
      [Term.op "choose"]
      (Term.nat 0) := by
  discharge_collapse_cert

/-! ## 9. Three same-typed arguments: finite branch collapse -/

def Γ_sum3 : Context
  | "sum3" => some (Ty.arrow [Ty.nat, Ty.nat, Ty.nat] Ty.nat)
  | _ => none

def eval_sum3 : EvalOpEngine
  | "sum3", [Term.nat x, Term.nat y, Term.nat z] =>
      some (Term.nat (x + y + z))
  | _, _ => none

example :
    CollapseCert eval_sum3 Γ_sum3
      [Term.op "sum3", Term.nat 1, Term.nat 2, Term.nat 3]
      (Term.nat 6) := by
  discharge_collapse_cert

/-! ## 10. Expected failure: noncommutative arity-three evaluator -/

def Γ_sub3 : Context
  | "sub3" => some (Ty.arrow [Ty.nat, Ty.nat, Ty.nat] Ty.nat)
  | _ => none

def eval_sub3 : EvalOpEngine
  | "sub3", [Term.nat x, Term.nat y, Term.nat z] =>
      some (Term.nat (x - y - z))
  | _, _ => none

/-
This should fail: admissible branches do not all collapse to `Term.nat 6`.
Uncomment when testing failure diagnostics.
-/
-- example :
--     CollapseCert eval_sub3 Γ_sub3
--       [Term.op "sub3", Term.nat 10, Term.nat 3, Term.nat 1]
--       (Term.nat 6) := by
--   discharge_collapse_cert

/-! ## 11. Direct collapse via generated certificate -/

example :
    CollapsesTo eval_add Γ_add
      [Term.op "add", Term.nat 2, Term.nat 3]
      (Term.nat 5) := by
  apply eval_by_cert
  discharge_collapse_cert

/-! ## Projective admissibility extension -/

def Γ_add1_projective : Context
  | "add1" => some (Ty.arrow [Ty.nat] Ty.nat)
  | _ => none

def eval_add1_projective : EvalOpEngine
  | "add1", [Term.nat n] => some (Term.nat (n + 1))
  | _, _ => none

/--
warning: projective admissibility ignored unused argument:
  Term.str "bad"
selected branch:
  add1 30
-/
#guard_msgs (warning, substring := true) in
example :
    CollapseCert eval_add1_projective Γ_add1_projective
      [Term.op "add1", Term.nat 30, Term.str "bad"]
      (Term.nat 31) := by
  discharge_collapse_cert

def eval_add1_projective_const : EvalOpEngine
  | "add1", [Term.nat _] => some (Term.nat 0)
  | _, _ => none

/--
warning: projective admissibility produced multiple branches with unused arguments:
  add1 30, unused: 9
  add1 9, unused: 30
-/
#guard_msgs (warning, substring := true) in
example :
    CollapseCert eval_add1_projective_const Γ_add1_projective
      [Term.op "add1", Term.nat 30, Term.nat 9]
      (Term.nat 0) := by
  discharge_collapse_cert

end CollapseCertExamples
