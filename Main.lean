import Socket

def client (arg : String) : IO Unit := do
  let sock ← Socket.mk .inet .stream
  let sa : Socket.SockAddr4 := .v4 (.mk 127 0 0 1) 8888
  sock.connect sa
  let bytes := arg.toUTF8
  let _ ← sock.send bytes
  let recv ← sock.recv 4096
  if recv.size == 0 then
    return ()
  let str := String.fromUTF8Unchecked recv
  assert! str == arg

def handle (client : Socket) : IO Unit := do
  let recv ← client.recv 4096
  if recv.size == 0 then
    return ()
  let _ ← client.send recv
  IO.println "Done handling"

def server : IO Unit := do
  let sock ← Socket.mk .inet .stream
  let sa : Socket.SockAddr4 := .v4 (.mk 127 0 0 1) 8888
  sock.bind sa
  sock.listen 1
  while true do
    let (client, _sa) ← sock.accept
    handle client
  return ()

def main (args : List String) : IO Unit := do
  let mode := args.get! 0
  if mode == "client" then
    client <| args.get! 1
  else if mode == "server" then
    server
  else
    IO.println "Unknown mode"
    return ()
