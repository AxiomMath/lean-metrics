import LemmaCmd.Syntax

/-! A `lemma` declared under its own namespace, as Batteries declares it. -/

lemma one_add_one : 1 + 1 = 2 := rfl

@[simp] lemma two_mul' (n : Nat) : 2 * n = n + n := by omega
