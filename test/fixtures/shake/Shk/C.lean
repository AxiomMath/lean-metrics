module

public import Lean.Elab.Command
public import Shk.A

public section

open Lean in
/-- A command that expands to nothing. -/
macro "noop_cmd" : command => `(section end)
