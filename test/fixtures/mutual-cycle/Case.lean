mutual
unsafe def a (n : Nat) : Nat := b n
unsafe def b (n : Nat) : Nat := a n
end
