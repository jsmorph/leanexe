import Lake
open Lake DSL

package "leanexe" where
  version := v!"0.1.0"

lean_lib LeanExe where

@[default_target]
lean_exe "lean-wasm" where
  root := `Main
