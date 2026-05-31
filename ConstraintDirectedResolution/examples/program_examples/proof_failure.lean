import program

program_module ProofFailure where
context
  pair : nat -> nat -> nat
engine
  (fun
    | "pair", [Term.nat x, Term.nat y] => some (Term.nat (10 * x + y))
    | _, _ => none)
program
  [pair, 1, 2]
end

/--
error: program evaluation failed at index 0: Could not collapse ambiguity.

Expression:
  [op "pair", 1, 2]

Admissible branches:
  pair(1, 2)
  pair(2, 1)

Unresolved branch:
  pair(2, 1)

Failed proof obligation:
  evalOp "pair" [2, 1]
    =
  evalOp "pair" [1, 2]

No ambiguity-collapse certificate could be constructed.
-/
#guard_msgs in
#run_program
