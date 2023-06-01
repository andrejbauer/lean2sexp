import Lake
open Lake DSL

package «lean2sexp» {
  -- add package configuration options here
  moreLeanArgs := #["-DautoImplicit=false"]
}

lean_lib Sexp {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean2sexp» {
  root := `Main
  supportInterpreter := true
}
