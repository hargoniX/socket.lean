import Alloy.C

open scoped Alloy.C

alloy c section

#include <lean/lean.h>
#include <string.h>
#include <fcntl.h>
#include <stdbool.h>

#ifdef _WIN32

#include <winsock.h>
#pragma comment(lib, "ws2_32.lib")

#else -- _WIN32

#include <errno.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <arpa/inet.h>
#include <netinet/in.h>

#endif -- _WIN32

struct socket_wrapper {
  int fd;
  bool closed;

  -- whether the fd should be closed by finalize()
  -- false if the fd is externally managed, eg by a parent process like systemd
  bool owned;
};

end

/--
A platform specific socket type. The usual main interaction points with this type are:
1. `Socket.mk` to create a `Socket`
2. `Socket.connect` to use a `Socket` as a client to connect somewhere
3. `Socket.bind`, `Socket.listen` and finally `Socket.accept` to host a server with a `Socket`
-/
alloy c opaque_extern_type Socket => struct socket_wrapper where
  finalize(ptr) :=
    struct socket_wrapper* sock = (struct socket_wrapper*)ptr;
    if (sock->owned && !sock->closed) {
      close(sock->fd);
    }
    free(sock);

namespace Socket

alloy c enum AddressFamily => int
| unix => AF_UNIX
| inet => AF_INET
| inet6 => AF_INET6
deriving Inhabited

abbrev AddresFamily.local : AddressFamily := AddressFamily.unix

-- TODO: NONBLOCK and CLOEXEC
alloy c enum Typ => int
| stream => SOCK_STREAM
| dgram => SOCK_DGRAM
| seqpacket => SOCK_SEQPACKET
| raw => SOCK_RAW
| rdm => SOCK_RDM
deriving Inhabited

/--
Create a `Socket` that:
- uses the address family specified with `address` in order to identify its peers
- uses the communication protocol specified with `type` to talk to its peers
- optionally the socket can be configured to act in a non blocking fashion via `blocking`

A `Socket` is automatically closed once Lean decides to free it so you
do not necessarily have to take care of this.
-/
alloy c extern "lean_mk_socket"
def mk (family : @& AddressFamily) (type : @& Typ) (blocking : Bool := true) : IO Socket :=
  int af = of_lean<AddressFamily>(family);
  int typ = of_lean<Typ>(type);
  struct socket_wrapper* sock = malloc(sizeof(struct socket_wrapper));
  sock->owned = true;
  sock->closed = false;
  sock->fd = socket(af, typ, 0);
  if (sock->fd < 0) {
    free(sock);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    if (blocking == 0) {
      if(fcntl(sock->fd, O_NONBLOCK) < 0) {
        free(sock);
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
      }
    }
    return lean_io_result_mk_ok(to_lean<Socket>(sock));
  }

/--
Create a `Socket` from a raw file descriptor.
- `fd`: The file descriptor
- `isOwned`: specifies whether the file descriptor should be considered owned by
  the `Socket`, in which case it will be closed when the socket is finalized.

WARNING: Only use this function if you know what you're doing.
In most cases, you probably want `Socket.mk`. This function was created
specifically for dealing with parent processes which pass sockets to our
process via the file descriptor table. In this case, the lifecycle of the
socket is probably managed by the parent process, so `isOwned` should be
`false`.

The implementation assumes that the provided file descriptor hasn't been closed.
-/
alloy c extern "lean_socket_from_fd"
def fromFd (fd : UInt32) (isOwned : Bool := false) : IO Socket :=
  int i_fd = (int)fd;

  -- Ensure the FD is valid
  if (fcntl(i_fd, F_GETFD) < 0) {
      return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  }

  struct socket_wrapper* sock = malloc(sizeof(struct socket_wrapper));
  sock->owned = isOwned;
  sock->closed = false;
  sock->fd = i_fd;
  return lean_io_result_mk_ok(to_lean<Socket>(sock));

/--
Close `socket`, this terminates the connection to its peer if it had one.
Closing a `Socket` means that it will be unusable for further operations as
its file descriptor gets invalidated. Thus any further operation on a closed
`Socket`, including closing it again, will throw an error.
-/
alloy c extern "lean_close_socket"
def close (socket : @& Socket) : IO Unit :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  } else {
    if (close(sock->fd) < 0) {
      return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    } else {
      sock->closed = true;
      return lean_io_result_mk_ok(lean_box(0));
    }
  }

alloy c opaque_extern_type SockAddr4 => struct sockaddr_in where
  finalize(ptr) := free(ptr)

alloy c opaque_extern_type SockAddr6 => struct sockaddr_in6 where
  finalize(ptr) := free(ptr)

alloy c opaque_extern_type SockAddrUnix => struct sockaddr_un where
  finalize(ptr) := free(ptr)

-- TODO: ToString/FromString
/--
Representation of an IPv4 address, create with `IPv4Addr.mk`.
-/
def IPv4Addr := UInt32

/--
This creates the IPv4 address `o1.o2.o3.o4`.
-/
def IPv4Addr.mk (o1 o2 o3 o4 : UInt8) : IPv4Addr :=
  o1.toUInt32 <<< 24 ||| o2.toUInt32 <<< 16 ||| o3.toUInt32 <<< 8 ||| o4.toUInt32

/--
Representaiton of an IPv6 address, create with `IPv4Addr.mk`
-/
def IPv6Addr := { xs : ByteArray // xs.size = 16 }

-- TODO: ToString/FromString
/--
This creates the IPv6 address `h1:h2:h3:h4:h5:h6:h7:h8`.
-/
def IPv6Addr.mk (h1 h2 h3 h4 h5 h6 h7 h8 : UInt16) : IPv6Addr := Id.run do
  let mut arr := ByteArray.emptyWithCapacity 16
  let push16 (h : UInt16) (arr : ByteArray) :=
    let p1 := (h >>> 8).toUInt8
    let p2 := h.toUInt8
    arr.push p1 |>.push p2
  arr := push16 h1 arr
  arr := push16 h2 arr
  arr := push16 h3 arr
  arr := push16 h4 arr
  arr := push16 h5 arr
  arr := push16 h6 arr
  arr := push16 h7 arr
  arr := push16 h8 arr
  return  ⟨arr, by trivial⟩

/--
Create an IPv4 socket address from:
- an IPv4 address
- a port

`SockAddr4` can be coerced to `SockAddr` so it is usually not necessary
to call the `SockAddr.v4Addr` constructor by hand.
-/
alloy c extern "lean_mk_sockaddr_in"
def SockAddr4.v4 (ip : IPv4Addr) (port : UInt16) : SockAddr4 :=
  struct sockaddr_in* sa = malloc(sizeof(struct sockaddr_in));
  sa->sin_family = AF_INET;
  sa->sin_port = htons(port);
  sa->sin_addr.s_addr = htonl(ip);
  return to_lean<SockAddr4>(sa);

/--
Create an IPv6 socket address from
- an IPv6 address
- a port
- optionally a configuration for flow info
- optionally a scope id

`SockAddr6` can be coerced to `SockAddr` so it is usually not necessary
to call the `SockAddr.v6Addr` constructor by hand.
-/
alloy c extern "lean_mk_sockaddr_in6"
def SockAddr6.v6 (ip : @& IPv6Addr) (port : UInt16) (flowinfo : UInt32 := 0) (scopeId : UInt32 := 0) : SockAddr6 :=
  struct sockaddr_in6* sa = (struct sockaddr_in6*) malloc(sizeof(struct sockaddr_in6));
  sa->sin6_family = AF_INET6;
  sa->sin6_port = htons(port);
  sa->sin6_flowinfo = htonl(flowinfo);
  memcpy(sa->sin6_addr.s6_addr, lean_sarray_cptr(ip), 16);
  sa->sin6_scope_id = scopeId;
  return to_lean<SockAddr6>(sa);

/--
Create a UNIX domain socket address from a file path.

`SockAddrUnix` can be coerced to `SockAddr` so it is usually not necessary
to call the `SockAddr.unixAddr` constructor by hand.
-/
alloy c extern "lean_mk_sockaddr_un"
def SockAddrUnix.unix (path : @& System.FilePath) : SockAddrUnix :=
  struct sockaddr_un* sa = (struct sockaddr_un*) malloc(sizeof(struct sockaddr_un));
  sa->sun_family = AF_UNIX;
  strncpy(sa->sun_path, lean_string_cstr(path), sizeof(sa->sun_path) - 1);
  return to_lean<SockAddrUnix>(sa);

/--
An address that can be used by a `Socket` to identify its peers.
-/
inductive SockAddr where
/--
IPv4 address
-/
| v4Addr (addr : SockAddr4)
/--
IPv6 address
-/
| v6Addr (addr : SockAddr6)
/--
UNIX domain socket address
-/
| unixAddr (addr : SockAddrUnix)

instance : Coe SockAddr4 SockAddr where
  coe sa := .v4Addr sa

instance : Coe SockAddr6 SockAddr where
  coe sa := .v6Addr sa

instance : Coe SockAddrUnix SockAddr where
  coe sa := .unixAddr sa

alloy c extern "lean_sockaddr_in_family"
def SockAddr4.family (addr : @& SockAddr4) : AddressFamily :=
  return to_lean<AddressFamily>(of_lean<SockAddr4>(addr)->sin_family);

alloy c extern "lean_sockaddr_in6_family"
def SockAddr6.family (addr : @& SockAddr6) : AddressFamily :=
  return to_lean<AddressFamily>(of_lean<SockAddr6>(addr)->sin6_family);

alloy c extern "lean_sockaddr_un_family"
def SockAddrUnix.family (addr : @& SockAddrUnix) : AddressFamily :=
  return to_lean<AddressFamily>(of_lean<SockAddrUnix>(addr)->sun_family);

/--
Get the `AddressFamily` of a `SockAddr`.
-/
def SockAddr.family (addr : SockAddr) : AddressFamily :=
  match addr with
  | .v4Addr sa | .v6Addr sa | .unixAddr sa => sa.family

alloy c extern "lean_sockaddr_in_port"
def SockAddr4.port (addr : @& SockAddr4) : UInt16 :=
  return ntohs(of_lean<SockAddr4>(addr)->sin_port);

alloy c extern "lean_sockaddr_in6_port"
def SockAddr6.port (addr : @& SockAddr6) : UInt16 :=
  return ntohs(of_lean<SockAddr6>(addr)->sin6_port);

/--
Get the port of a `SockAddr`. This is not a total function
as UNIX domain socket addresses do not have a port.
-/
def SockAddr.port? (addr : SockAddr) : Option UInt16 :=
  match addr with
  | .v4Addr sa | .v6Addr sa => sa.port
  | .unixAddr .. => none

alloy c extern "lean_sockaddr_in_addr"
def SockAddr4.addr (addr : @& SockAddr4) : String :=
  char string[INET_ADDRSTRLEN];
  inet_ntop(AF_INET, &of_lean<SockAddr4>(addr)->sin_addr, string, INET_ADDRSTRLEN);
  return lean_mk_string(string);

alloy c extern "lean_sockaddr_in6_addr"
def SockAddr6.addr (addr : @& SockAddr6) : String :=
  char string[INET6_ADDRSTRLEN];
  inet_ntop(AF_INET6, &of_lean<SockAddr6>(addr)->sin6_addr, string, INET6_ADDRSTRLEN);
  return lean_mk_string(string);

alloy c extern "lean_sockaddr_un_addr"
def SockAddrUnix.addr (addr : @& SockAddrUnix) : String :=
  struct sockaddr_un* sun = of_lean<SockAddrUnix>(addr);
  char string[sizeof(sun->sun_path)];
  inet_ntop(AF_UNIX, &sun->sun_path, string, sizeof(string));
  return lean_mk_string(string);

/--
Get the actual address behind a `SockAddr` as a string.
This corresponds to:
- the IPv4 address for `SockAddr4`
- the IPv6 address for `SockAddr6`
- the file path for `SockAddrUnix`
-/
def SockAddr.addr (addr : SockAddr) : String :=
  match addr with
  | .v4Addr sa | .v6Addr sa | .unixAddr sa => sa.addr

/--
Connect to a `SockAddr` with a `Socket`. This is sets up the `Socket`
as a client which can
- send data using `Socket.send`
- receive answers using `Socket.recv`
- close the connection using `Socket.close`
-/
alloy c extern "lean_socket_connect"
def connect (socket : @& Socket) (addr : @& SockAddr) : IO Unit :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }

  int tag = lean_obj_tag(addr);
  int err = 0;
  struct sockaddr* sa = (struct sockaddr *)(lean_get_external_data(lean_ctor_get(addr, 0)));

  switch (tag) {
    case 0:
      err = connect(sock->fd, sa, sizeof(struct sockaddr_in));
      break;
    case 1:
      err = connect(sock->fd, sa, sizeof(struct sockaddr_in6));
      break;
    case 2:
      err = connect(sock->fd, sa, sizeof(struct sockaddr_un));
      break;
    default:
      return lean_panic_fn(lean_box(0), lean_mk_string("illegal C value"));
  }

  if (err < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }

/--
Send the bytes from `buf` to the peer of `socket`.
-/
alloy c extern "lean_socket_send"
def send (socket : @& Socket) (buf : @& ByteArray) : IO USize :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }

  ssize_t bytes = send(sock->fd, lean_sarray_cptr(buf), lean_sarray_size(buf), 0);
  if (bytes < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box_usize(bytes));
  }

-- TOOD: support flags
/--
This function is similar to `Socket.connect`. However there is no need for the initial
`Socket.connect` call as the address of the peer is passed in via `addr`.
-/
alloy c extern "lean_socket_sendto"
def sendto (socket : @& Socket) (buf : @& ByteArray) (addr : @& SockAddr) : IO USize :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  int tag = lean_obj_tag(addr);
  ssize_t bytes = 0;
  struct sockaddr* sa = (struct sockaddr *)(lean_get_external_data(lean_ctor_get(addr, 0)));

  switch (tag) {
    case 0:
      bytes = sendto(
        sock->fd,
        lean_sarray_cptr(buf),
        lean_sarray_size(buf),
        0,
        sa,
        sizeof(struct sockaddr_in)
      );
      break;
    case 1:
      bytes = sendto(
        sock->fd,
        lean_sarray_cptr(buf),
        lean_sarray_size(buf),
        0,
        sa,
        sizeof(struct sockaddr_in6)
      );
      break;
    case 2:
      bytes = sendto(
        sock->fd,
        lean_sarray_cptr(buf),
        lean_sarray_size(buf),
        0,
        sa,
        sizeof(struct sockaddr_un)
      );
      break;
    default:
      return lean_panic_fn(lean_box(0), lean_mk_string("illegal C value"));
  }

  if (bytes < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box_usize(bytes));
  }

-- TODO: support flags
/--
Receive up to `maxBytes` bytes from the peer of `socket` in a `ByteArray`.
-/
alloy c extern "lean_socket_recv"
def recv (socket : @& Socket) (maxBytes : USize) : IO ByteArray :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  lean_object *buf = lean_alloc_sarray(1, 0, maxBytes);
  ssize_t recvBytes = recv(sock->fd, lean_sarray_cptr(buf), maxBytes, 0);
  if (recvBytes < 0) {
      return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
      lean_sarray_object* arrObj = lean_to_sarray(buf);
      arrObj->m_size = recvBytes;
      return lean_io_result_mk_ok(buf);
  }

/--
Bind `socket` to `addr`. This is the first in 3 steps to use it as as a server.
The remaining two are:
1. `Socket.listen`
2. `Socket.accept`
-/
alloy c extern "lean_socket_bind"
def bind (socket : @& Socket) (addr : @& SockAddr) : IO Unit :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  int tag = lean_obj_tag(addr);
  int err = 0;
  struct sockaddr* sa = (struct sockaddr *)(lean_get_external_data(lean_ctor_get(addr, 0)));

  switch (tag) {
    case 0:
      err = bind(sock->fd, sa, sizeof(struct sockaddr_in));
      break;
    case 1:
      err = bind(sock->fd, sa, sizeof(struct sockaddr_in6));
      break;
    case 2:
      err = bind(sock->fd, sa, sizeof(struct sockaddr_un));
      break;
    default:
      return lean_panic_fn(lean_box(0), lean_mk_string("illegal C value"));
  }

  if (err < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }

/--
Let `socket` listen on the `SocketAddr` that it was previously bound to using `Socket.bind`.
The `backlog` argument tells the OS how many connections it should keep queued while waiting to
accepted. If more than `backlog` connections are pending on `socket` the clients will be denied
connection.

This is the second in 3 steps to set `socket` use it as a server, the last one is `Socket.accept`.
-/
alloy c extern "lean_socket_listen"
def listen (socket : @& Socket) (backlog : UInt32) : IO Unit :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  if (listen(sock->fd, backlog) < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }

/--
Wait until a new client connects to `socket` after it has been configured as a server using
`Socket.bind` and `Socket.listen`. This returns both a new `Socket` to communicate with the
client and the `SockAddr` of the client.
-/
alloy c extern "lean_socket_accept"
def accept (socket : @& Socket) : IO (Socket × SockAddr) :=
  socklen_t saSize = sizeof(struct sockaddr);

  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }

  struct socket_wrapper* newSock = (struct socket_wrapper*) malloc(sizeof(struct socket_wrapper));
  newSock->owned = true;
  newSock->closed = false;
  struct sockaddr* sa = (struct sockaddr*) malloc(saSize);

  newSock->fd = accept(sock->fd, sa, &saSize);

  if (newSock->fd < 0) {
    free(sa);
    free(newSock);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, to_lean<Socket>(newSock));
    lean_object* leanSa;
    switch (sa->sa_family) {
      case AF_INET:
        leanSa = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddr4>((struct sockaddr_in*)sa));
        break;
      case AF_INET6:
        leanSa = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddr6>((struct sockaddr_in6*)sa));
        break;
      case AF_UNIX:
        leanSa = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddrUnix>((struct sockaddr_un*)sa));
        break;
      default:
        return lean_panic_fn(lean_box(0), lean_mk_string("accept only supports INET, INET6 and UNIX right now"));
    }
    lean_ctor_set(pair, 1, leanSa);
    return lean_io_result_mk_ok(pair);
  }

/--
Get the `SockAddr` of the `Socket` connected to `socket`.
-/
alloy c extern "lean_socket_getpeername"
def getpeername (socket : @& Socket) : IO SockAddr :=
  socklen_t saSize = sizeof(struct sockaddr);

  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  struct sockaddr* sa = (struct sockaddr*) malloc(saSize);

  if (getpeername(sock->fd, sa, &saSize) < 0) {
    free(sa);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    lean_object* leanSa;
    switch (sa->sa_family) {
      case AF_INET:
        leanSa = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddr4>((struct sockaddr_in*)sa));
        break;
      case AF_INET6:
        leanSa = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddr6>((struct sockaddr_in6*)sa));
        break;
      case AF_UNIX:
        leanSa = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddrUnix>((struct sockaddr_un*)sa));
        break;
      default:
        return lean_panic_fn(lean_box(0), lean_mk_string("getpeername only supports INET, INET6 and UNIX right now"));
    }
    return lean_io_result_mk_ok(leanSa);
  }

/--
Get the `SockAddr` of `socket`.
-/
alloy c extern "lean_socket_getsockname"
def getsockname (socket : @& Socket) : IO SockAddr :=
  socklen_t saSize = sizeof(struct sockaddr);

  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  struct sockaddr* sa = (struct sockaddr*) malloc(saSize);

  if (getsockname(sock->fd, sa, &saSize) < 0) {
    free(sa);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    lean_object* leanSa;
    switch (sa->sa_family) {
      case AF_INET:
        leanSa = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddr4>((struct sockaddr_in*)sa));
        break;
      case AF_INET6:
        leanSa = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddr6>((struct sockaddr_in6*)sa));
        break;
      case AF_UNIX:
        leanSa = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(leanSa, 0, to_lean<SockAddrUnix>((struct sockaddr_un*)sa));
        break;
      default:
        return lean_panic_fn(lean_box(0), lean_mk_string("getsockname only supports INET, INET6 and UNIX right now"));
    }
    return lean_io_result_mk_ok(leanSa);
  }

alloy c enum ShutdownHow => int
| read => SHUT_RD
| write => SHUT_WR
| readWrite => SHUT_RDWR
deriving Inhabited

/--
Partially or fully shutdown `socket`. Depending on the value of `how` this can deny further
writes, reads or both.
-/
alloy c extern "lean_socket_shutdown"
def shutdown (socket : @& Socket) (how : ShutdownHow) : IO Unit :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  int cHow = of_lean<ShutdownHow>(how);

  if (shutdown(sock->fd, cHow) < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }

-- TODO: refactor once alloy gets `unsafe`


/--
Get the underlying file descriptor. This API is safe iff:
1. You make sure to keep `socket` alive while using the file descriptor.
2. You do not `close` or otherwise invalidate the file descriptor.
-/
alloy c extern "lean_socket_fd"
unsafe def getFd (socket : @& Socket) : IO UInt32 :=
  struct socket_wrapper* sock = of_lean<Socket>(socket);
  if (sock->closed) {
    return lean_io_result_mk_error(lean_decode_io_error(EBADF, NULL));
  }
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)sock->fd));
