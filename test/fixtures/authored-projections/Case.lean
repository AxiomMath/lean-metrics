class Box where
  value : Nat

/-- This is an authored function, not a parent projection. -/
def Box.toNat (b : Box) : Nat := b.value

theorem read_box (b : Box) : b.toNat = b.value := rfl
