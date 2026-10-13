namespace Lean.Meta
/-- Authored user code. -/
def customThing : Nat := 2
end Lean.Meta
/-- Another declaration. -/
def consumer := Lean.Meta.customThing
