import Lake
open Lake DSL

package Erdos279 where
  version := v!"0.1.0"

require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @
  "4373fe8a5bb2a26d60fbeb3d0f99d9d1aba3d824"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "32d24245c7a12ded17325299fd41d412022cd3fe"

@[default_target]
lean_lib Erdos279
