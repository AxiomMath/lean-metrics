theorem termPlain : (0 : Nat) = 0 := rfl
theorem termParen : (0 : Nat) = 0 := (rfl)
theorem termTyped : (0 : Nat) = 0 := (rfl : (0 : Nat) = 0)
theorem termOption : (0 : Nat) = 0 := set_option pp.universes true in rfl
theorem termOpen : (0 : Nat) = 0 := open Nat in rfl
theorem tacticPlain : (0 : Nat) = 0 := by rfl
theorem tacticParen : (0 : Nat) = 0 := (by rfl)
theorem tacticTyped : (0 : Nat) = 0 := (by rfl : (0 : Nat) = 0)
theorem tacticOption : (0 : Nat) = 0 := set_option pp.universes true in by rfl
theorem tacticOpen : (0 : Nat) = 0 := open Nat in by rfl
