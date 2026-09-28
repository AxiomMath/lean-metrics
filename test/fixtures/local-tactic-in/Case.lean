import Lean
set_option maxRecDepth 1000 in
local macro "finish_it" : tactic => `(tactic| trivial)
theorem localProof : True := by finish_it
