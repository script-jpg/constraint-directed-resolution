/-
Diagnostic regression tests for `discharge_collapse_cert`.
-/

import checker

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

noncomputable section

namespace CollapseCertDiagnostics

def Γ_checkExpect : Context
  | "checkExpect" => some (Ty.arrow [Ty.nat, Ty.nat] (Ty.tuple [Ty.nat, Ty.nat]))
  | _ => none

def eval_checkExpect : EvalOpEngine
  | "checkExpect", [expected, actual] =>
      some (Term.tupleVal [expected, actual])
  | _, _ => none

/--
error: Could not collapse ambiguity.

Expression:
  [op "checkExpect", actual, expected]

Admissible branches:
  checkExpect(actual, expected)
  checkExpect(expected, actual)

Unresolved branch:
  checkExpect(expected, actual)

Failed proof obligation:
  evalOp "checkExpect" [expected, actual]
    =
  evalOp "checkExpect" [actual, expected]

No ambiguity-collapse certificate could be constructed.
-/
#guard_msgs (error, substring := true) in
example (expected actual : Nat) :
    CollapseCert eval_checkExpect Γ_checkExpect
      [Term.op "checkExpect", Term.nat actual, Term.nat expected]
      (Term.tupleVal [Term.nat actual, Term.nat expected]) := by
  discharge_collapse_cert

def Γ_sub3_diag : Context
  | "sub3" => some (Ty.arrow [Ty.nat, Ty.nat, Ty.nat] Ty.nat)
  | _ => none

def eval_sub3_diag : EvalOpEngine
  | "sub3", [Term.nat x, Term.nat y, Term.nat z] =>
      some (Term.nat (x - y - z))
  | _, _ => none

/--
error: Could not collapse ambiguity.

Expression:
  [op "sub3", 10, 3, 1]

Admissible branches:
  sub3(10, 3, 1)
  sub3(10, 1, 3)
  sub3(3, 10, 1)
  sub3(3, 1, 10)
  sub3(1, 10, 3)
  sub3(1, 3, 10)

Unresolved branch:
  sub3(3, 10, 1)

Failed proof obligation:
  evalOp "sub3" [3, 10, 1]
    =
  evalOp "sub3" [10, 3, 1]

No ambiguity-collapse certificate could be constructed.
-/
#guard_msgs (error, substring := true) in
example :
    CollapseCert eval_sub3_diag Γ_sub3_diag
      [Term.op "sub3", Term.nat 10, Term.nat 3, Term.nat 1]
      (Term.nat 6) := by
  discharge_collapse_cert

def Γ_known_only : Context
  | "known" => some (Ty.arrow [Ty.nat] Ty.nat)
  | _ => none

def eval_known_only : EvalOpEngine
  | "known", [Term.nat n] => some (Term.nat n)
  | _, _ => none

/--
error: Could not collapse ambiguity.

Expression:
  [op "missing", 1]

Admissible branches:
  <none>

No admissible branch could be constructed.
-/
#guard_msgs (error, substring := true) in
example :
    CollapseCert eval_known_only Γ_known_only
      [Term.op "missing", Term.nat 1]
      (Term.nat 1) := by
  discharge_collapse_cert

/--
error: discharge_collapse_cert failed
failed goal:
True
-/
#guard_msgs (error, substring := true) in
example : True := by
  discharge_collapse_cert

end CollapseCertDiagnostics
