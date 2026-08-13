import Mathlib

namespace MathlibPlus.Combinatorics.Claim44788

/-- A family of local card maps is pairwise coherent when the maps attached to
any two distinct cards agree away from those two cards. -/
def pairwiseCoherent {ι β : Type*} [DecidableEq ι]
    (π : ι → ι → β) : Prop :=
  ∀ i j, i ≠ j → ∀ x, x ≠ i → x ≠ j → π i x = π j x

end MathlibPlus.Combinatorics.Claim44788
