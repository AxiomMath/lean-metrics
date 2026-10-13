module
public section
class Marker (α : Type) where
  value : α

@[expose, instance_reducible] def registered : Marker Nat := ⟨0⟩
attribute [instance] registered
attribute [instance] registered

class Law : Prop where
  proof : True

section
private local instance localNamed : Marker Bool := ⟨true⟩
local instance : Marker Unit := ⟨()⟩
local instance propNamed : Law := ⟨True.intro⟩
end
