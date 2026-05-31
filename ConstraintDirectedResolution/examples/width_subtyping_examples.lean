/-
Examples for ambiguity-branch width subtyping.
-/

import checker

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

noncomputable section

namespace WidthSubtypingExamples

def Γ_add1 : Context
  | "add1" => some (Ty.arrow [Ty.nat] Ty.nat)
  | _ => none

example :
    enumerateAdmissible Γ_add1 [Term.op "add1", Term.nat 30, Term.str "bad"] =
      [{ opName := "add1",
         realizedArgs := { args := [Term.nat 30], unused := [Term.str "bad"], synthesized := [] } }] := by
  simp [Γ_add1, enumerateAdmissible, enumerateRealizedArgs,
    enumerateRealizedArgsFrom, pickAllExact, filterOps,
    filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf]

example :
    enumerateAdmissible Γ_add1 [Term.op "add1", Term.nat 30, Term.nat 9] =
      [{ opName := "add1",
         realizedArgs := { args := [Term.nat 30], unused := [Term.nat 9], synthesized := [] } },
       { opName := "add1",
         realizedArgs := { args := [Term.nat 9], unused := [Term.nat 30], synthesized := [] } }] := by
  simp [Γ_add1, enumerateAdmissible, enumerateRealizedArgs,
    enumerateRealizedArgsFrom, pickAllExact, filterOps,
    filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf]

def eval_add1 : EvalOpEngine
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
    CollapseCert eval_add1 Γ_add1
      [Term.op "add1", Term.nat 30, Term.str "bad"]
      (Term.nat 31) := by
  discharge_collapse_cert

def eval_add1_const : EvalOpEngine
  | "add1", [Term.nat _] => some (Term.nat 0)
  | _, _ => none

/--
warning: projective admissibility produced multiple branches with unused arguments:
  add1 30, unused: 9
  add1 9, unused: 30
-/
#guard_msgs (warning, substring := true) in
example :
    CollapseCert eval_add1_const Γ_add1
      [Term.op "add1", Term.nat 30, Term.nat 9]
      (Term.nat 0) := by
  discharge_collapse_cert

end WidthSubtypingExamples
