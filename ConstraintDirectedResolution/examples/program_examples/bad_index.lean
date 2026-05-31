import program

program_module BadIndex where
context
  inc : nat -> nat
engine
  (fun
    | "inc", [Term.nat x] => some (Term.nat (x + 1))
    | _, _ => none)
program
  [inc, seq(@3, 1)]
end

/--
error: failed to resolve program expression at index 0
-/
#guard_msgs in
#run_program
