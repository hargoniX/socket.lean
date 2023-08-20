import Socket

def client : IO Unit := do
  let sock ← Socket.mk .inet .stream
  let sa : Socket.SockAddr4 := .v4 (.mk 127 0 0 1) 8888
  sock.connect sa
  while true do
    let stdin ← IO.getStdin
    let input ← stdin.getLine
    let bytes := input.toUTF8
    let _ ← sock.send bytes
    let recv ← sock.recv 4096
    let str := String.fromUTF8Unchecked recv
    IO.println s!"Got: {str.trimRight}"

def server : IO Unit := do
  let sock ← Socket.mk .inet .stream 
  let sa : Socket.SockAddr4 := .v4 (.mk 127 0 0 1) 8888
  sock.bind sa
  sock.listen 1
  let (client, _sa) ← sock.accept
  while true do
    let recv ← client.recv 4096 
    let str := String.fromUTF8Unchecked recv
    IO.println s!"Got: {str.trimRight}, echoing"
    let _ ← client.send recv

def main (args : List String) : IO Unit := do
  let mode := args.get! 0
  if mode == "client" then
    client
  else if mode == "server" then
    server
  else
    IO.println "Unknown mode"
    return ()  