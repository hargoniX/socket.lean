import Socket

def mkSocketV4: IO (Socket × Socket.SockAddr) := do
  let sock ← Socket.mk .inet .stream
  pure (sock, Socket.SockAddr4.v4 (.mk 127 0 0 1) 8888)

def mkSocketV6: IO (Socket × Socket.SockAddr) := do
  let sock ← Socket.mk .inet6 .stream
  pure (sock, Socket.SockAddr6.v6 (.mk 0 0 0 0 0 0 0 1) 8888)

def mkSocketUnix: IO (Socket × Socket.SockAddr) := do
  let sock ← Socket.mk .unix .stream
  pure (sock, Socket.SockAddrUnix.unix "./unix.addr")


def client (arg : String) (input : Socket × Socket.SockAddr): IO Unit := do
  let (sock, sa) := input
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

def server (input : Socket × Socket.SockAddr) : IO Unit := do
  let (sock, sa) := input
  sock.bind sa
  sock.listen 1
  while true do
    let (client, _sa) ← sock.accept
    handle client
  return ()

def main (args : List String) : IO Unit := do
  let mode := args.get! 0
  if mode == "client" then do
    let type := args.get! 1
    if type == "v4" then
        mkSocketV4 >>= client (args.get! 2)
    else if type == "v6" then
        mkSocketV6 >>= client (args.get! 2)
    else if type == "unix" then
        mkSocketUnix >>= client (args.get! 2)
    else
        mkSocketV4 >>= client type

  else if mode == "server" then
    let type := args.get! 1
    if type == "unix" then
      mkSocketUnix >>= server
    else if type == "v6" then
      mkSocketV6 >>= server
    else
      mkSocketV4 >>= server

  else
    IO.println "Unknown mode"
    return ()
