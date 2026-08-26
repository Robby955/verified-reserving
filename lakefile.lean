import Lake
open Lake DSL

package «verified-reserving» where
  -- Machine-checked claims reserving and actuarial risk mathematics in Lean 4.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

-- Documentation and blueprint tooling, only when built with `-Kenv=dev`.
meta if get_config? env == some "dev" then
  require «doc-gen4» from git
    "https://github.com/leanprover/doc-gen4" @ "v4.32.2"

meta if get_config? env == some "dev" then
  require checkdecls from git
    "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib VerifiedReserving where
  roots := #[`VerifiedReserving]
