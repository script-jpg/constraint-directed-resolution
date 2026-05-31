import program

program_module ManualProofs where
context
  inc : nat -> nat
engine
  (fun
    | "inc", [Term.nat x] => some (Term.nat (x + 1))
    | _, _ => none)
program
  [inc, 4]
manual_proofs
  | 0 => by
      discharge_collapse_cert
end

#run_program
