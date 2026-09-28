def a : Nat := 1
def b : Nat := a + 1
def c : Nat := a + b
theorem t : c = 3 := rfl
theorem u : c = 3 ∧ True := ⟨t, trivial⟩
