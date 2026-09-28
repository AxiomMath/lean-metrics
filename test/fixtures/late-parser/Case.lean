import Lean
theorem original : True := by trivial
syntax (name := shadowTheorem) (priority := high) "theorem " ident " : " "True" " := " "by " "trivial" : command
