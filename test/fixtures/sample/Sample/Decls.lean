import Sample.Lemma

namespace Sample

/-- A structure. -/
structure Point where
  x : Nat
  y : Nat
  deriving Repr

class Size (α : Type) where
  size : α → Nat

instance : Size Point := ⟨fun p => p.x + p.y⟩

inductive Color where
  | red | green

abbrev N := Nat

@[reducible] def two : N := 2

@[simp] theorem two_eq : two = 2 := rfl

lemma two_add {n : Nat} : two + n = n + 2 := Nat.add_comm _ _

example : two = 2 := rfl

opaque secret : Nat

axiom trustMe : 1 = 1

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

open Nat in
theorem succ_ne (n : Nat) : succ n ≠ 0 := Nat.succ_ne_zero n

def h1 (x : Nat) ⦃y : Nat⦄ [Inhabited Nat] : Nat := x + y

def countdown (n : Nat) : Nat :=
  if n = 0 then 0 else countdown (n - 1)
termination_by n
decreasing_by omega

end Sample
