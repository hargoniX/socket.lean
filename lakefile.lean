import Lake
open Lake DSL System

require alloy from git "https://github.com/tydeu/lean4-alloy/" @ "master"

package «socket» { }

@[default_target]
lean_exe socket_test {
  root := `Main
  moreLeancArgs := #["-fPIC"]
}

module_data alloy.c.o.export : FilePath
module_data alloy.c.o.noexport : FilePath

lean_lib «Socket» {
  precompileModules := true
  nativeFacets := fun shouldExport =>
    if shouldExport then
      #[Module.oExportFacet, `module.alloy.c.o.export]
    else
      #[Module.oNoExportFacet, `module.alloy.c.o.noexport]
  moreLeancArgs := #["-fPIC"]
}
