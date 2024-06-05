import Lake
open Lake DSL

package «lean-cutting-planes» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

lean_lib «LeanCuttingPlanes» where

@[test_runner]
script tests do
  return 0


@[default_target]
lean_exe «lean-cutting-planes» where
  root := `Main
