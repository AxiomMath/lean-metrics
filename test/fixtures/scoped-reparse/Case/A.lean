import Case.N

theorem original : True := by trivial

open Foo in
example : ⟪1⟫ = 2 := rfl

namespace Bar
scoped notation "⟦⟦" x "⟧⟧" => x
end Bar

open Bar
example : ⟦⟦1⟧⟧ = 1 := rfl

namespace X
open Foo
example : ⟪2⟫ = 3 := rfl
end X

namespace W
open Iso
example : ⌈1⌉ = 1 := rfl
structure Iso where
  x : Nat
end W

structure Q where
  x : Nat
-- `open` fails as a whole unless `Q` is a namespace, which leaves `Foo` inactive
open Q Foo
example : ⟪1⟫ = 2 := rfl
