import Alloy.C
import Lean
import Std.Data.Array.Basic

namespace Alloy.C
open Lean

alloy c include <lean/lean.h>

alloy c section
static inline void noop_foreach(void *mod, b_lean_obj_arg fn) {}
end

scoped syntax "alloy" "c" "enum" ident " : " ident "translators" ident " ↔ " ident "where" ("| " ident " = " ident)+ : command

macro_rules
| `(command| alloy c enum $name:ident : $cType:ident translators $leanToC:ident ↔ $cToLean:ident where $[| $leanVariant:ident = $cVariant:ident]*) => do
  let ffiType ←
    if leanVariant.size <= 2^8 then
      pure <| mkIdent `uint8_t
    else if leanVariant.size <= 2^16 then
      pure <| mkIdent `uint16_t
    else if leanVariant.size <= 2^32 then
      pure <| mkIdent `uint32_t
    else
      Macro.throwError s!"Enum {name} has more than 2^32 variants, this is not supported"
  let counter := Array.range leanVariant.size |>.map (Syntax.mkNumLit <| toString ·)
  `(
    inductive $name : Type where $[ | $leanVariant:ident]*
    alloy c section
      static inline $cType $leanToC:ident($ffiType:ident arg) {
        switch (arg) {
          $[
            case $counter:constExpr:
              return $cVariant;
          ]*
          default:
            lean_panic_fn(lean_box(-1), lean_mk_string("illegal C value"));
            return -1;
        }
      }

      static inline $ffiType $cToLean:ident($cType:ident arg) {
        switch (arg) {
          $[
            case $cVariant:constExpr:
              return $counter;
          ]*
          default:
            lean_panic_fn(lean_box(-1), lean_mk_string("illegal Lean value"));
            return -1;
        }
      }
    end
   )

scoped syntax "alloy" "c" "alloc" ident " = " cTypeSpec "as" ident "translators" ident " ↔ " ident "finalize" ident : command

macro_rules
| `(command| alloy c alloc $name:ident = $cName:cTypeSpec as $externClass:ident translators $leanToC:ident ↔ $cToLean:ident finalize $finalizer:ident) =>
  let nonemptyType := mkIdent <| name.getId.append `nonemptyType
  `(
    opaque $nonemptyType : NonemptyType
    def $name : Type := NonemptyType.type $nonemptyType
    instance : Nonempty $name := Subtype.property $nonemptyType

    alloy c section
      static lean_external_class* $externClass:ident = NULL;

      static void $finalizer:ident(void* ptr) {
        free(($cName:cTypeSpec*)ptr);
      }

      static inline lean_object* $cToLean:ident($cName:cTypeSpec* ptr) {
        if ($externClass:ident == NULL) {
          $externClass:ident = lean_register_external_class($finalizer:ident, noop_foreach);
        }
        return lean_alloc_external($externClass:ident, ptr);
      }

      static inline $cName:cTypeSpec* $leanToC:ident(b_lean_obj_arg ptr) {
        return ($cName:cTypeSpec*)(lean_get_external_data(ptr));
      }
    end
  )

end Alloy.C


opaque Socket.nonemptyType : NonemptyType

/--
A platform specific socket type. The usual main interaction points with this type are:
1. `Socket.mk` to create a `Socket`
2. `Socket.connect` to use a `Socket` as a client to connect somewhere
3. `Socket.bind`, `Socket.listen` and finally `Socket.accept` to host a server with a `Socket`
-/
def Socket : Type := Socket.nonemptyType.type

instance : Nonempty Socket := Socket.nonemptyType.property

namespace Socket
open scoped Alloy.C

alloy c section
#include <string.h>
#include <fcntl.h>

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

end

alloy c enum AddressFamily : int translators lean_to_socket_af ↔ socket_af_to_lean where
| unix = AF_UNIX
| inet = AF_INET
| inet6 = AF_INET6

deriving instance Inhabited for AddressFamily

abbrev AddresFamily.local : AddressFamily := AddressFamily.unix

-- TODO: NONBLOCK and CLOEXEC
alloy c enum Typ : int translators lean_to_socket_type ↔ socket_type_to_lean where
| stream = SOCK_STREAM
| dgram = SOCK_DGRAM
| seqpacket = SOCK_SEQPACKET
| raw = SOCK_RAW
| rdm = SOCK_RDM

deriving instance Inhabited for Typ

alloy c section

static lean_external_class *g_socket_external_class = NULL;

static void socket_finalize(void* ptr) {
  int* fd = (int*)ptr;
  close(*fd);
  free(fd);
}

static inline lean_object* socket_to_lean(int* s) {
  if (g_socket_external_class == NULL) {
    g_socket_external_class = lean_register_external_class(socket_finalize, noop_foreach);
  }
  return lean_alloc_external(g_socket_external_class, s);
}

static inline int* lean_to_socket(b_lean_obj_arg s) {
  return (int*)(lean_get_external_data(s));
}

end

/--
Create a `Socket` that:
- uses the address family specified with `address` in order to identify its peers
- uses the communication protocol specified with `type` to talk to its peers
- optionally the socket can be configured to act in a non blocking fashion via `blocking`

A `Socket` is automatically closed once Lean decides to free it so you
do not necessarily have to take care of this.
-/
alloy c extern "lean_mk_socket"
def mk (family : @& AddressFamily) (type : @& Typ) (blocking : Bool := true) : IO Socket := {
  int af = lean_to_socket_af(family);
  int typ = lean_to_socket_type(type);
  int* fd = malloc(sizeof(int));
  *fd = socket(af, typ, 0);
  if (*fd < 0) {
    free(fd);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    if (blocking == 0) {
      if(fcntl(*fd, O_NONBLOCK) < 0) {
        free(fd);
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
      }
    }
    return lean_io_result_mk_ok(socket_to_lean(fd));
  }
}

/--
Close `socket`, this terminates the connection to its peer if it had one.
-/
alloy c extern "lean_close_socket"
def close (socket : @& Socket) : IO Unit := {
  int fd = *lean_to_socket(socket);
  if (close(fd) < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }
}

alloy c alloc SockAddr4 = struct sockaddr_in as g_sockaddr_in_external_class translators lean_to_sockaddr_in ↔ sockaddr_in_to_lean  finalize sockaddr_in_finalize
alloy c alloc SockAddr6 = struct sockaddr_in6 as g_sockaddr_in6_external_class translators lean_to_sockaddr_in6 ↔ sockaddr_in6_to_lean finalize sockaddr_in6_finalize
alloy c alloc SockAddrUnix = struct sockaddr_un as g_sockaddr_un_external_class translators lean_to_sockaddr_un ↔ sockaddr_un_to_lean  finalize sockaddr_un_finalize

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
  let mut arr := ByteArray.mkEmpty 16
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
  return  ⟨arr, sorry⟩


/--
Create an IPv4 socket address from:
- an IPv4 address
- a port

`SockAddr4` can be coerced to `SockAddr` so it is usually not necessary
to call the `SockAddr.v4Addr` constructor by hand.
-/
alloy c extern "lean_mk_sockaddr_in"
def SockAddr4.v4 (ip : IPv4Addr) (port : UInt16) : SockAddr4 := {
  struct sockaddr_in* sa = malloc(sizeof(struct sockaddr_in));
  sa->sin_family = AF_INET;
  sa->sin_port = htons(port);
  sa->sin_addr.s_addr = htonl(ip);
  return sockaddr_in_to_lean(sa);
}

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
def SockAddr6.v6 (ip : @& IPv6Addr) (port : UInt16) (flowinfo : UInt32 := 0) (scopeId : UInt32 := 0) : SockAddr6 := {
  struct sockaddr_in6* sa = malloc(sizeof(struct sockaddr_in6));
  sa->sin6_family = AF_INET6;
  sa->sin6_port = htons(port);
  sa->sin6_flowinfo = htonl(flowinfo);
  memcpy(sa->sin6_addr.s6_addr, lean_sarray_cptr(ip), 16);
  sa->sin6_scope_id = scopeId;
  return sockaddr_in6_to_lean(sa);
}

/--
Create a UNIX domain socket address from a file path.

`SockAddrUnix` can be coerced to `SockAddr` so it is usually not necessary
to call the `SockAddr.unixAddr` constructor by hand.
-/
alloy c extern "lean_mk_sockaddr_un"
def SockAddrUnix.unix (path : @& System.FilePath) : SockAddrUnix := {
  struct sockaddr_un* sa = malloc(sizeof(struct sockaddr_un));
  sa->sun_family = AF_UNIX;
  strncpy(sa->sun_path, lean_string_cstr(path), sizeof(sa->sun_path) - 1);
  return sockaddr_un_to_lean(sa);
}

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
def SockAddr4.family (addr : @& SockAddr4) : AddressFamily := {
  return (lean_to_sockaddr_in(lean_ctor_get(addr, 0)))->sin_family;
}

alloy c extern "lean_sockaddr_in6_family"
def SockAddr6.family (addr : @& SockAddr6) : AddressFamily := {
  return (lean_to_sockaddr_in6(lean_ctor_get(addr, 0)))->sin6_family;
}

alloy c extern "lean_sockaddr_un_family"
def SockAddrUnix.family (addr : @& SockAddrUnix) : AddressFamily := {
  return (lean_to_sockaddr_un(lean_ctor_get(addr, 0)))->sun_family;
}

/--
Get the `AddressFamily` of a `SockAddr`.
-/
def SockAddr.family (addr : SockAddr) : AddressFamily :=
  match addr with
  | .v4Addr sa | .v6Addr sa | .unixAddr sa => sa.family

alloy c extern "lean_sockaddr_in_port"
def SockAddr4.port (addr : @& SockAddr4) : UInt16 := {
  return ntohs((lean_to_sockaddr_in(addr))->sin_port);
}

alloy c extern "lean_sockaddr_in6_port"
def SockAddr6.port (addr : @& SockAddr6) : UInt16 := {
  return ntohs((lean_to_sockaddr_in6(addr))->sin6_port);
}

/--
Get the port of a `SockAddr`. This is not a total function
as UNIX domain socket addresses do not have a port. 
-/
def SockAddr.port? (addr : SockAddr) : Option UInt16 :=
  match addr with
  | .v4Addr sa | .v6Addr sa => sa.port
  | .unixAddr .. => none

alloy c extern "lean_sockaddr_in_addr"
def SockAddr4.addr (addr : @& SockAddr4) : String := {
  char string[INET_ADDRSTRLEN];
  inet_ntop(AF_INET, &(lean_to_sockaddr_in(addr))->sin_addr, string, INET_ADDRSTRLEN);
  return lean_mk_string(string);
}

alloy c extern "lean_sockaddr_in6_addr"
def SockAddr6.addr (addr : @& SockAddr6) : String := {
  char string[INET6_ADDRSTRLEN];
  inet_ntop(AF_INET6, &(lean_to_sockaddr_in6(addr))->sin6_addr, string, INET6_ADDRSTRLEN);
  return lean_mk_string(string);
}

alloy c extern "lean_sockaddr_un_addr"
def SockAddrUnix.addr (addr : @& SockAddrUnix) : String := {
  struct sockaddr_un* sun = lean_to_sockaddr_un(addr);
  char string[sizeof(sun->sun_path)];
  inet_ntop(AF_UNIX, &sun->sun_path, string, sizeof(string));
  return lean_mk_string(string);
}

/--
Get the actual address behind a `SockAddr` as a string.
This corresponds to:
- the IPv4 address for `SockAddr4`
- the IPv6 address for `SockAddr4`
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
def connect (socket : @& Socket) (addr : @& SockAddr) : IO Unit := {
  int fd = *lean_to_socket(socket);
  int tag = lean_obj_tag(addr);
  int err = 0;
  struct sockaddr* sa = (struct sockaddr *)(lean_to_sockaddr_in(lean_ctor_get(addr, 0)));

  switch (tag) {
    case 0:
      err = connect(fd, sa, sizeof(struct sockaddr_in));
      break;
    case 1:
      err = connect(fd, sa, sizeof(struct sockaddr_in6));
      break;
    default:
      return lean_panic_fn(lean_box(0), lean_mk_string("illegal C value"));
  }

  if (err < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }
}

/--
Send the bytes from `buf` to the peer of `socket`.
-/
alloy c extern "lean_socket_send"
def send (socket : @& Socket) (buf : @& ByteArray) : IO USize := {
  int fd = *lean_to_socket(socket);
  ssize_t bytes = send(fd, lean_sarray_cptr(buf), lean_sarray_size(buf), 0);
  if (bytes < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box_usize(bytes));
  }
}

-- TOOD: support flags
/--
This function is similar to `Socket.connect`. However there is no need for the initial
`Socket.connect` call as the address of the peer is passed in via `addr`.
-/
alloy c extern "lean_socket_sendto"
def sendto (socket : @& Socket) (buf : @& ByteArray) (addr : @& SockAddr) : IO USize := {
  int fd = *lean_to_socket(socket);
  int tag = lean_obj_tag(addr);
  ssize_t bytes = 0;
  struct sockaddr* sa = (struct sockaddr *)(lean_to_sockaddr_in(lean_ctor_get(addr, 0)));

  switch (tag) {
    case 0:
      bytes = sendto(
        fd,
        lean_sarray_cptr(buf),
        lean_sarray_size(buf),
        0,
        sa,
        sizeof(struct sockaddr_in)
      );
      break;
    case 1:
      bytes = sendto(
        fd,
        lean_sarray_cptr(buf),
        lean_sarray_size(buf),
        0,
        sa,
        sizeof(struct sockaddr_in6)
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
}

-- TODO: support flags
/--
Receive up to `maxBytes` bytes from the peer of `socket` in a `ByteArray`.
-/
alloy c extern "lean_socket_recv"
def recv (socket : @& Socket) (maxBytes : USize) : IO ByteArray := {
  int fd = *lean_to_socket(socket);
  lean_object *buf = lean_alloc_sarray(1, 0, maxBytes);
  ssize_t recvBytes = recv(fd, lean_sarray_cptr(buf), maxBytes, 0);
  if (recvBytes < 0) {
      return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
      lean_sarray_object* arrObj = lean_to_sarray(buf);
      arrObj->m_size = recvBytes;
      return lean_io_result_mk_ok(buf);
  }
}

/--
Bind `socket` to `addr`. This is the first in 3 steps to use it as as a server.
The remaining two are:
1. `Socket.listen`
2. `Socket.accept`
-/
alloy c extern "lean_socket_bind"
def bind (socket : @& Socket) (addr : @& SockAddr) : IO Unit := {
  int fd = *lean_to_socket(socket);
  int tag = lean_obj_tag(addr);
  int err = 0;
  struct sockaddr* sa = (struct sockaddr *)(lean_to_sockaddr_in(lean_ctor_get(addr, 0)));

  switch (tag) {
    case 0:
      err = bind(fd, sa, sizeof(struct sockaddr_in));
      break;
    case 1:
      err = bind(fd, sa, sizeof(struct sockaddr_in6));
      break;
    default:
      return lean_panic_fn(lean_box(0), lean_mk_string("illegal C value"));
  }

  if (err < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }
}

/--
Let `socket` listen on the `SocketAddr` that it was previously bound to using `Socket.bind`.
The `backlog` argument tells the OS how many connections it should keep queued while waiting to
accepted. If more than `backlog` connections are pending on `socket` the clients will be denied
connection.

This is the second in 3 steps to set `socket` use it as a server, the last one is `Socket.accept`.
-/
alloy c extern "lean_socket_listen"
def listen (socket : @& Socket) (backlog : UInt32) : IO Unit := {
  int fd = *lean_to_socket(socket);
  if (listen(fd, backlog) < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }
}

/--
Wait until a new client connects to `socket` after it has been configured as a server using
`Socket.bind` and `Socket.listen`. This returns both a new `Socket` to communicate with the
client and the `SockAddr` of the client.
-/
alloy c extern "lean_socket_accept"
def accept (socket : @& Socket) : IO (Socket × SockAddr) := {
  socklen_t saSize;

  int fd = *lean_to_socket(socket);
  int* newFd = malloc(sizeof(int));
  struct sockaddr* sa = malloc(sizeof(struct sockaddr));

  *newFd = accept(fd, sa, &saSize);

  if (*newFd < 0) {
    free(sa);
    free(newFd);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, socket_to_lean(newFd));
    lean_object* leanSa;
    switch (sa->sa_family) {
      case AF_INET:
        leanSa = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_in_to_lean((struct sockaddr_in*)sa));
        break;
      case AF_INET6:
        leanSa = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_in6_to_lean((struct sockaddr_in6*)sa));
        break;
      case AF_UNIX:
        leanSa = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_un_to_lean((struct sockaddr_un*)sa));
        break;
      default:
        return lean_panic_fn(lean_box(0), lean_mk_string("accept only supports INET, INET6 and UNIX right now"));
    }
    lean_ctor_set(pair, 1, leanSa);
    return lean_io_result_mk_ok(pair);
  }
}

/--
Get the `SockAddr` of the `Socket` connected to `socket`.
-/
alloy c extern "lean_socket_getpeername"
def getpeername (socket : @& Socket) : IO SockAddr := {
  socklen_t saSize;

  int fd = *lean_to_socket(socket);
  struct sockaddr* sa = malloc(sizeof(struct sockaddr));

  if (getpeername(fd, sa, &saSize) < 0) {
    free(sa);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    lean_object* leanSa;
    switch (sa->sa_family) {
      case AF_INET:
        leanSa = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_in_to_lean((struct sockaddr_in*)sa));
        break;
      case AF_INET6:
        leanSa = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_in6_to_lean((struct sockaddr_in6*)sa));
        break;
      case AF_UNIX:
        leanSa = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_un_to_lean((struct sockaddr_un*)sa));
        break;
      default:
        return lean_panic_fn(lean_box(0), lean_mk_string("getpeername only supports INET, INET6 and UNIX right now"));
    }
    return lean_io_result_mk_ok(leanSa);
  }
}

/--
Get the `SockAddr` of `socket`.
-/
alloy c extern "lean_socket_getsockname"
def getsockname (socket : @& Socket) : IO SockAddr := {
  socklen_t saSize;

  int fd = *lean_to_socket(socket);
  struct sockaddr* sa = malloc(sizeof(struct sockaddr));

  if (getsockname(fd, sa, &saSize) < 0) {
    free(sa);
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    lean_object* leanSa;
    switch (sa->sa_family) {
      case AF_INET:
        leanSa = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_in_to_lean((struct sockaddr_in*)sa));
        break;
      case AF_INET6:
        leanSa = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_in6_to_lean((struct sockaddr_in6*)sa));
        break;
      case AF_UNIX:
        leanSa = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(leanSa, 0, sockaddr_un_to_lean((struct sockaddr_un*)sa));
        break;
      default:
        return lean_panic_fn(lean_box(0), lean_mk_string("getsockname only supports INET, INET6 and UNIX right now"));
    }
    return lean_io_result_mk_ok(leanSa);
  }
}

alloy c enum ShutdownHow : int translators lean_to_socket_shutdown ↔ socket_shutdown_to_lean where
| read = SHUT_RD
| write = SHUT_WR
| readWrite = SHUT_RDWR

/--
Partially or fully shutdown `socket`. Depending on the value of `how` this can deny further
writes, reads or both.
-/
alloy c extern "lean_socket_shutdown"
def shutdown (socket : @& Socket) (how : ShutdownHow) : IO Unit := {
  int fd = *lean_to_socket(socket);
  int cHow = lean_to_socket_shutdown(how);

  if (shutdown(fd, cHow) < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }
}

end Socket
