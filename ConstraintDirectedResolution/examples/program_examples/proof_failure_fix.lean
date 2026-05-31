import program

program_module ProofFailureFix where
context
  pair : scale : nat -> nat -> nat
engine
  (fun
    | "pair", [Term.wrap "scale" (Term.nat x), Term.nat y] => some (Term.nat (10 * x + y))
    | _, _ => none)
program
  [pair, 1, wrap("scale", 2)]
end

#run_program
