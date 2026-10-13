inductive A | a
inductive B | b
set_option maxRecDepth 1000 in
deriving instance Repr, DecidableEq for A, B
