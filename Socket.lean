import Alloy.C
import Lean
import Std.Data.Array.Basic

namespace Socket

open scoped Alloy.C
open Lean

syntax "alloy" "c" "enum" ident " : " ident "translators" ident " ↔ " ident "where" ("| " ident " = " ident)+ : command

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
            case $counter:num:
              return $cVariant:ident;
          ]*
          default:
            lean_panic_fn(lean_box(-1), lean_mk_string("illegal C value"));
        }
      }

      static inline $ffiType $cToLean:ident($cType:ident arg) {
        switch (arg) {
          $[
            case $cVariant:ident:
              return $counter:num;
          ]*
          default:
            lean_panic_fn(lean_box(-1), lean_mk_string("illegal Lean value"));
        }
      }
    end
   )

alloy c include <lean/lean.h> <sys/socket.h> <errno.h> <unistd.h>

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
    g_socket_external_class = lean_register_external_class(socket_finalize, NULL);
  }
  return lean_alloc_external(g_socket_external_class, s);
}

static inline int* lean_to_socket(b_lean_obj_arg s) {
  return (int*)(lean_get_external_data(s));
}

end

opaque T.nonemptyType : NonemptyType
def T : Type := T.nonemptyType.type
instance : Nonempty T := T.nonemptyType.property

alloy c extern "lean_mk_socket"
def mk (family : AddressFamily) (type : Typ) : IO T := {
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

end Socket
