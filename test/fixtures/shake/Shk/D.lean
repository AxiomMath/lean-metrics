module

-- uses `a` only through `b`'s module; `Shk.A` is also imported directly
public import Shk.A
public import Shk.B
public import Shk.C

public section

def d : Nat := b + a

noop_cmd
