initialize do
  let p ← IO.Process.spawn { cmd := "echo", args := #["child chatter"] }
  discard p.wait
def value : Nat := 1
