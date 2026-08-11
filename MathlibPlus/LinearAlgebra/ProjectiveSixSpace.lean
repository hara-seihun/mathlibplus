import Mathlib

namespace MathlibPlus.LinearAlgebra.ProjectiveSixSpace

open scoped LinearAlgebra.Projectivization

section

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/--
Claim 27913.  The seven surviving coordinates are modeled as the vector space
`Fin 7 → ZMod 5`, so its projectivization is `ℙ⁶(𝔽₅)`.  Mathlib's exact
projectivization cardinality formula gives the claimed 19,531 points.
-/
theorem cardinality :
    Nat.card (ℙ (ZMod 5) (Fin 7 → ZMod 5)) = 19531 := by
  have hfinrank : Module.finrank (ZMod 5) (Fin 7 → ZMod 5) = 7 := by
    simp
  rw [Projectivization.card_of_finrank (ZMod 5) (Fin 7 → ZMod 5) hfinrank]
  norm_num [Finset.sum_range_succ]

end

end MathlibPlus.LinearAlgebra.ProjectiveSixSpace
