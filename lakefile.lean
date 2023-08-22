import Lake
open Lake DSL

require alloy from git "https://github.com/tydeu/lean4-alloy/" @ "master"
require std from git "https://github.com/leanprover/std4" @ "main"

package «socket» { }

@[default_target]
lean_exe socket_test {
  root := `Main
  moreLeancArgs := #["-fPIC"]
  --moreLinkArgs := if System.Platform.isWindows then #["-lwsock32"] else #[]
}

module_data alloy.c.o : BuildJob FilePath
lean_lib «Socket» {
  --precompileModules := true
  nativeFacets := #[Module.oFacet, `alloy.c.o]
  moreLeancArgs := #["-fPIC"]
  --moreLinkArgs := if System.Platform.isWindows then #["-lwsock32"] else #[]
}
