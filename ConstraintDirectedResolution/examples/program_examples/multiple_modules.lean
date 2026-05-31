import program

program_module First where
context
  inc : nat -> nat
engine
  (fun
    | "inc", [Term.nat x] => some (Term.nat (x + 1))
    | _, _ => none)
program
  [inc, 1]
end

/--
error: only one program_module is allowed per source file
-/
#guard_msgs in
program_module Second where
context
  inc : nat -> nat
engine
  (fun
    | "inc", [Term.nat x] => some (Term.nat (x + 1))
    | _, _ => none)
program
  [inc, 2]
end
