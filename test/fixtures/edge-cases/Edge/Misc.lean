def U1 : Type 1 := Type
def U2 : Type 2 := Type 1

class C (α : Type) where
  op : α → α

instance instCNat : C Nat where
  op := id

inductive I1 | a
inductive I2 | b

deriving instance Repr, DecidableEq for I1, I2

theorem t1 : 2 + 2 = 4 := by decide -kernel
theorem t2 (n : Nat) : n + 0 = n := by simp -arith

namespace A
namespace B
def x : Nat := 0
end B
end A

namespace A.B
def y : Nat := 1
end A.B
