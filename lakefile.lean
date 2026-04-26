import Lake
open Lake DSL

package qanaryPaper6 where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "322515540d7f"

-- Sibling dependencies: Papers 3-5
require qanaryUniversal from ".." / "qanary-universal"
require qanaryPaper4 from ".." / "qanary-paper4"
require qanaryPaper5 from ".." / "qanary-paper5"

@[default_target]
lean_lib QanaryPaper6
