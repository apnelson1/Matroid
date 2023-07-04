import Lake
open Lake DSL

package «matroid» where 
  moreServerArgs := #["-DrelaxedAutoImplicit=false","-Dpp.unicode.fun=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Matroid» {
  moreLeanArgs := #["-DrelaxedAutoImplicit=false"]
}
