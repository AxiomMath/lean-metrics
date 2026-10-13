def a : Nat := 1
private theorem p : a = 1 := rfl
theorem q : a = 1 := p
