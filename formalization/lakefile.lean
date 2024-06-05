import Lake
open Lake DSL

package «formalization» where
  -- add package configuration options here

lean_lib «Formalization» where
  -- add library configuration options here

@[default_target]
lean_exe «formalization» where
  root := `Main
