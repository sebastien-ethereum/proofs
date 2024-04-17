import Lake
open Lake DSL

package «proofs» where
  -- add package configuration options here

lean_lib «Proofs» where
  -- add library configuration options here

@[default_target]
lean_exe «proofs» where
  root := `Main
