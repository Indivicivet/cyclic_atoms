import Lake
open Lake DSL

package cyclicAtoms {
  -- add package configuration options here
}

lean_lib CyclicAtoms {
  -- add library configuration options here
}

@[default_target]
lean_exe cyclicAtoms {
  root := `Main
}
