import Lake
open Lake DSL

package «plfl» where
  -- add package configuration options here
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.0"

lean_lib «Plfl» where
  -- add library configuration options here
