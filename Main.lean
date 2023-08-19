import Socket

def main : IO Unit := do
  let sock ← Socket.mk .inet .stream
  return ()
