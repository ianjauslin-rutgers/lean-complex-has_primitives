import Lake
open Lake DSL

package «HasPrimitives» where
  -- add package configuration options here

lean_lib «HasPrimitives» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"fccca5a"

meta if get_config? env = some "dev" then require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "53ecc22"

@[default_target]
lean_exe «hasprimitives» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
