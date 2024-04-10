import Lake
open Lake DSL

package «lean-cutting-planes» where
  -- add package configuration options here

lean_lib «LeanCuttingPlanes» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-cutting-planes» where
  root := `Main
