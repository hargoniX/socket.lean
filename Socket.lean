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
def Socket : Type := Socket.nonemptyType.type
instance : Nonempty Socket := Socket.nonemptyType.property

namespace Socket
open scoped Alloy.C

alloy c include <sys/socket.h> <errno.h> <unistd.h>

alloy c enum AddressFamily : int translators lean_to_socket_af ↔ socket_af_to_lean where
| unix = AF_UNIX
| inet = AF_INET
| ax25 = AF_AX25
| ipx = AF_IPX
| appletalk = AF_APPLETALK
| netrom = AF_NETROM
| bridge = AF_BRIDGE
| atmpvc = AF_ATMPVC
| x25 = AF_X25
| inet6 = AF_INET6
| rose = AF_ROSE
| decnet = AF_DECnet
| netbeui = AF_NETBEUI
| security = AF_SECURITY
| key = AF_KEY
| netlink = AF_NETLINK
| packet = AF_PACKET
| econet = AF_ECONET
| atmsvc = AF_ATMSVC
| rds = AF_RDS
| irda = AF_IRDA
| pppox = AF_PPPOX
| wanpipe = AF_WANPIPE
| llc = AF_LLC
| ib = AF_IB
| mpls = AF_MPLS
| can = AF_CAN
| tipc = AF_TIPC
| bluetooth = AF_BLUETOOTH
| iucv = AF_IUCV
| rxrpc = AF_RXRPC
| isdn = AF_ISDN
| phonet = AF_PHONET
| ieee802154 = AF_IEEE802154
| caif = AF_CAIF
| alg = AF_ALG
| vsock = AF_VSOCK
| kcm = AF_KCM
| qipcrtr = AF_QIPCRTR
| smc = AF_SMC
| xdp = AF_XDP
| unspec = AF_UNSPEC

abbrev AddresFamily.local : AddressFamily := AddressFamily.unix

-- TODO: NONBLOCK and CLOEXEC
alloy c enum Typ : int translators lean_to_socket_type ↔ socket_type_to_lean where
| stream = SOCK_STREAM
| dgram = SOCK_DGRAM
| seqpacket = SOCK_SEQPACKET
| raw = SOCK_RAW
| rdm = SOCK_RDM
| packet = SOCK_PACKET

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

alloy c extern "lean_mk_socket"
def mk (family : AddressFamily) (type : Typ) : IO Socket := {
  int af = lean_to_socket_af(family);
  int typ = lean_to_socket_type(type);
  int* fd = malloc(sizeof(int));
  *fd = socket(af, typ, 0);
  if (*fd < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(socket_to_lean(fd));
  }
}

alloy c extern "lean_close_socket"
def close (socket : Socket) : IO Unit := {
  int fd = *lean_to_socket(socket);
  if (close(fd) < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box(0));
  }
}

alloy c include <netinet/in.h> <string.h>
-- TODO: projection functions
alloy c alloc SockAddr4 = struct sockaddr_in as g_sockaddr_in_external_class translators lean_to_sockaddr_in ↔ sockaddr_in_to_lean  finalize sockaddr_in_finalize
alloy c alloc SockAddr6 = struct sockaddr_in6 as g_sockaddr_in6_external_class translators lean_to_sockaddr_in6 ↔ sockaddr_in6_to_lean finalize sockaddr_in6_finalize

-- TODO: ToString/FromString
def IPv4Addr := UInt32
def IPv4Addr.mk (o1 o2 o3 o4 : UInt8) : IPv4Addr :=
  o1.toUInt32 <<< 24 ||| o2.toUInt32 <<< 16 ||| o3.toUInt32 <<< 8 ||| o4.toUInt32

def IPv6Addr := { xs : ByteArray // xs.size = 16 }

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

alloy c section
-- TODO: temporary until Mac fixes the malloc invocation in the lines below
typedef struct sockaddr_in sockaddr_in;
typedef struct sockaddr_in6 sockaddr_in6;

end

alloy c extern "lean_mk_sockaddr_in"
def SockAddr4.v4 (ip : IPv4Addr) (port : UInt16) : SockAddr4 := {
  struct sockaddr_in* sa = malloc(sizeof(sockaddr_in));
  sa->sin_family = AF_INET;
  sa->sin_port = htons(port);
  sa->sin_addr.s_addr = htonl(ip);
  return sockaddr_in_to_lean(sa);
}

alloy c extern "lean_mk_sockaddr_in6"
def SockAddr6.v6 (ip : IPv6Addr) (port : UInt16) (flowinfo : UInt32) (scopeId : UInt32) : SockAddr6 := {
  struct sockaddr_in6* sa = malloc(sizeof(sockaddr_in6));
  sa->sin6_family = AF_INET6;
  sa->sin6_port = htons(port);
  sa->sin6_flowinfo = htonl(flowinfo);
  memcpy(sa->sin6_addr.s6_addr, lean_sarray_cptr(ip), 16);
  sa->sin6_scope_id = scopeId;
  return sockaddr_in6_to_lean(sa);
}

inductive SockAddr where
| v4Addr (addr : SockAddr4)
| v6Addr (addr : SockAddr6)

instance : Coe SockAddr4 SockAddr where
  coe sa := .v4Addr sa

instance : Coe SockAddr6 SockAddr where
  coe sa := .v6Addr sa

alloy c extern "lean_socket_connect"
def connect (socket : Socket) (addr : SockAddr) : IO Unit := {
  int fd = *lean_to_socket(socket);
  int tag = lean_obj_tag(addr);
  int err = 0;
  struct sockaddr* sa = (struct sockaddr *)(lean_to_sockaddr_in(lean_ctor_get(addr, 0)));

  switch (tag) {
    case 0:
      err = connect(fd, sa, sizeof(sockaddr_in));
      break;
    case 1:
      err = connect(fd, sa, sizeof(sockaddr_in6));
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

-- TOOD: support flags
alloy c extern "lean_socket_send"
def send (socket : Socket) (buf : ByteArray) : IO USize := {
  int fd = *lean_to_socket(socket);
  ssize_t bytes = send(fd, lean_sarray_cptr(buf), lean_sarray_size(buf), 0);
  if (bytes < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  } else {
    return lean_io_result_mk_ok(lean_box_usize(bytes));
  }
}

-- TOOD: support flags
alloy c extern "lean_socket_sendto"
def sendto (socket : Socket) (buf : ByteArray) (addr : SockAddr) : IO USize := {
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
        sizeof(sockaddr_in)
      );
      break;
    case 1:
      bytes = sendto(
        fd,
        lean_sarray_cptr(buf),
        lean_sarray_size(buf),
        0,
        sa,
        sizeof(sockaddr_in6)
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
alloy c extern "lean_socket_recv"
def recv (socket : Socket) (maxBytes : USize) : IO ByteArray := {
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

end Socket
