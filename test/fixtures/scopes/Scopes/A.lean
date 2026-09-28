/-! Nesting reaches depth 2. -/

-- a line comment
namespace Outer
section
/-- A documented definition. -/
def one : Nat := 1 -- trailing comment
end
end Outer

/- a block comment /- nested -/ still inside -/
theorem one_eq : Outer.one = 1 := rfl
