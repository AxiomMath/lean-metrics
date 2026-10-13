def length : (xs : List Nat) → Nat
  | [] => 0
  | _ :: xs => length xs + 1
termination_by structural xs => xs
