import Lake
open Lake DSL

package «praos» where

lean_lib «Praos» where
  srcDir := "src"

require hoare from
  "../hoare"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.7.0"

require std from git
  "https://github.com/leanprover/std4"
  @ "v4.7.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec.git"

require Cli from git
  "https://github.com/leanprover/lean4-cli.git"
  @ "v2.2.0-lv4.7.0"

@[default_target]
lean_exe «praos» where
  root := `Main
  srcDir := "src"
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := false
