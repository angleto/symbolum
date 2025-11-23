import Lake
open Lake DSL

package «collatz-descent» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CollatzDescent» {
  -- add library configuration options here
}
