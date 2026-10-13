def inferred (n : Nat) : Nat :=
  if n = 0 then 0 else inferred (n - 1)
