module
public section

def annotated (n : Nat) : Nat :=
  if n = 0 then 0 else annotated (n - 1)
termination_by n
decreasing_by omega
