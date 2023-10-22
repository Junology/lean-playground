import Lake
open Lake DSL

package «lean-playground» where
  -- add package configuration options here

require std from git "https://github.com/leanprover/std4" @ "main"
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib «LeanPlayground» where
  -- add library configuration options here
