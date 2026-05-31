import program

program_module AutoSuccess where
context
  inc : nat -> nat
  sum : seq nat -> nat
  max : nat -> nat -> nat
  divide : num : nat -> nat -> nat
engine
  (fun
    | "inc", [Term.nat x] => some (Term.nat (x + 1))
    | "sum", [Term.seqVal head tail] =>
        let headVal := match head with | Term.nat n => n | _ => 0
        let tailSum := tail.foldl (fun acc t =>
          match t with
          | Term.nat n => acc + n
          | _ => acc) 0
        some (Term.nat (headVal + tailSum))
    | "max", [Term.nat a, Term.nat b] => some (Term.nat (max a b))
    | "divide", [Term.wrap "num" (Term.nat a), Term.nat b] => some (Term.nat (a / b))
    | _, _ => none)
program
  [inc, 1]
  [@0, inc]
  [@0, @1, max, "5"]
  [sum, seq(@0, @2, 10)]
  [divide, wrap("num", @3), 3]
end

#run_program
-- warning: projective admissibility produced multiple branches with unused arguments:
--   max 2 3, unused: Term.str "5"
--   max 3 2, unused: Term.str "5"
-- [Term.nat 2, Term.nat 3, Term.nat 3, Term.nat 15, Term.nat 5]
