import Sample.Decls

namespace Sample.Proofs

theorem t1 (a b : Nat) (h : a = b) : b = a := by
  have h' : b = a := h.symm
  exact h'

theorem t2 : 2 + 2 = 4 := by decide

theorem t3 : 10 < 20 := by
  decide +kernel

theorem t4 (n : Nat) : n + 0 = n := by
  simp

theorem t5 (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c :=
  calc a = b := h₁
    _ = c := h₂

theorem t6 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  obtain ⟨x, y⟩ : p ∧ q := ⟨hp, hq⟩
  exact ⟨x, y⟩

set_option maxHeartbeats 400000 in
theorem t7 : True := by
  trivial

set_option linter.unusedVariables false in
theorem t8 (unused : Nat) : True := trivial

theorem t10 (x : Nat) : True := by trivial

end Sample.Proofs
