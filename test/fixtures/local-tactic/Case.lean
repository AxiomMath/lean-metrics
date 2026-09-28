import Lean
section
local macro "finish_it" : tactic => `(tactic| trivial)
theorem localProof : True := by finish_it
end
