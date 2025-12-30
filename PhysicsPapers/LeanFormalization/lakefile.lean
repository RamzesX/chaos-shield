import Lake
open Lake DSL

package DiscreteSpacetime where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`linter.docPrime, false⟩,
    ⟨`diagnostics, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"

@[default_target]
lean_lib DiscreteSpacetime where
  globs := #[.submodules `DiscreteSpacetime]
