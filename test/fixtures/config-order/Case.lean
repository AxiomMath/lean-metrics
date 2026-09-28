theorem a : True := by decide (kernel := true)
theorem b : True := by decide +kernel -kernel
theorem c : True := by decide +kernel (kernel := false)
theorem d (n : Nat) : n + 0 = n := by simp (arith := true)
