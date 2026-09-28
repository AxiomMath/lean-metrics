import Sample.Proofs

open Lean Elab Command

/-- A macro whose body quotes tactics; those are not tactic calls. -/
macro "my_tac" : tactic => `(tactic| (simp; decide))

syntax "my_cmd" : command

elab_rules : command
  | `(my_cmd) => logInfo "hi"

my_cmd

#eval 1 + 1

def s : String := "-- not a comment /- nor this -/"

initialize counter : IO.Ref Nat ← IO.mkRef 0

section
local notation "𝟚" => (2 : Nat)

theorem two_local : 𝟚 = 2 := rfl
end
