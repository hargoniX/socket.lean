import Socket

def main : IO Unit := do
  let sock ← Socket.mk .inet .stream
  let sa : Socket.SockAddr4 := .v4 (.mk 127 0 0 1) 8888
  sock.connect sa
  let data := "Hello World\n".toUTF8
  let bytes ← sock.send data
  IO.println s!"Sent {bytes} greeting bytes"
  while true do
    let bytes ← sock.recv 4096
    let str := String.fromUTF8Unchecked bytes
    IO.println s!"Got: {str.trimRight}, echoing"
    let _ ← sock.send bytes
  return ()
