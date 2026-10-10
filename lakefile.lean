mport Lake
open Lake DSL

package «jsp-000690-lean» where
  srcDir := "."

@[default_target]
lean_lib «Jsp» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"
