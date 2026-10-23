import Lake
open Lake DSL

package «MSTNF» where

require "leanprover-community" / "mathlib" @ git "v4.14.0"

/-- Zero-import, Mathlib-free predicate form of the MST-NF core-object definitions. -/
@[default_target]
lean_lib «MSTNFDefsPred» where
  roots := #[`MSTNFDefsPred.MSTNFDefsPredMWE]

/-- Everything else: set-form definitions, the bridge, and the theory. Module names follow the directory layout. -/
@[default_target]
lean_lib «MSTNF» where
  globs := #[.submodules `MSTNF]
