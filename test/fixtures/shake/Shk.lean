module

-- `lake shake Shk` removes and adds: in `B`, `-A +A` (public to private); in `C`,
-- `-Lean.Elab.Command -A`; in `D`, `-A -B -C +C +B +A`; in `E`, `-B -Lean.Elab.Command +A`.

public import Shk.D
public import Shk.E
