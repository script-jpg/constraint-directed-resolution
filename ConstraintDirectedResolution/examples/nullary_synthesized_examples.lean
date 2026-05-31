import checker

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

noncomputable section

namespace NullarySynthesizedExamples

def Γ_ping : Context
  | "ping" => some (Ty.arrow [] Ty.nat)
  | _ => none

def noiseResidue : Multiset Term :=
  [Term.str "noise"]

def pingNoiseCall : RealizedCall :=
  { opName := "ping",
    realizedArgs := { args := [], unused := noiseResidue, synthesized := [] } }

example :
    enumerateAdmissible Γ_ping [Term.op "ping"] =
      [{ opName := "ping",
         realizedArgs := { args := [], unused := 0, synthesized := [] } }] := by rfl

example :
    enumerateAdmissible Γ_ping [Term.op "ping", Term.str "noise"] =
      [{ opName := "ping",
         realizedArgs := { args := [], unused := noiseResidue, synthesized := [] } }] := by rfl

example :
    pingNoiseCall ∈ enumerateAdmissible Γ_ping [Term.op "ping", Term.str "noise"] ↔
      Admissible Γ_ping [Term.op "ping", Term.str "noise"] pingNoiseCall :=
  enumerate_admissible_iff

example :
    Admissible Γ_ping [Term.op "ping", Term.str "noise"] pingNoiseCall ↔
      Admissible Γ_ping [Term.str "noise", Term.op "ping"] pingNoiseCall := by
  exact Admissible.perm_iff (List.Perm.swap _ _ _)

def eval_ping : EvalOpEngine
  | "ping", [] => some (Term.nat 1)
  | _, _ => none

example :
    CollapseCert eval_ping Γ_ping [Term.op "ping"] (Term.nat 1) := by
  discharge_collapse_cert

def Γ_limit : Context
  | "limit" => some (Ty.arrow [Ty.nat, Ty.option Ty.nat] Ty.nat)
  | _ => none

example :
    enumerateAdmissible Γ_limit [Term.op "limit", Term.nat 10, Term.none] =
      [{ opName := "limit",
         realizedArgs := { args := [Term.nat 10, Term.none], unused := 0, synthesized := [] } }] := by
  simp [Γ_limit, enumerateAdmissible, enumerateRealizedArgs,
    enumerateRealizedArgsFrom, pickAllExact, pickAllOption, optionArgMatches,
    filterOps, filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf]

example :
    enumerateAdmissible Γ_limit [Term.op "limit", Term.nat 10] =
      [{ opName := "limit",
         realizedArgs := { args := [Term.nat 10, Term.none], unused := 0, synthesized := [{ paramIndex := 1, term := Term.none }] } }] := by
  simp [Γ_limit, enumerateAdmissible, enumerateRealizedArgs,
    enumerateRealizedArgsFrom, pickAllExact, pickAllOption, optionArgMatches,
    filterOps, filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf]

example :
    enumerateAdmissible Γ_limit [Term.op "limit", Term.nat 10, Term.str "noise"] =
      [{ opName := "limit",
         realizedArgs := { args := [Term.nat 10, Term.none], unused := noiseResidue, synthesized := [{ paramIndex := 1, term := Term.none }] } }] := by
  simp [Γ_limit, noiseResidue, enumerateAdmissible, enumerateRealizedArgs,
    enumerateRealizedArgsFrom, pickAllExact, pickAllOption, optionArgMatches,
    filterOps, filterNonOps, Term.isOp, Term.isNonOp, Term.typeOf]

example :
    SynthesizedWellFormed [Ty.nat, Ty.option Ty.nat]
      [{ paramIndex := 1, term := Term.none }] := by
  constructor
  · intro x hx
    simp at hx
    rcases hx with rfl
    simp [SynthesizedWithinBounds]
  · simp [SynthesizedDistinct]

end NullarySynthesizedExamples
