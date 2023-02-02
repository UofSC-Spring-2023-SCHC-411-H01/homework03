import Lake
open Lake DSL

package «hw» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Hw» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4.git" @ "main"
