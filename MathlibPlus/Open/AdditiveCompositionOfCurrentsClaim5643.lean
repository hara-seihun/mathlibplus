import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

/-- Additive composition of the subset-sum currents of a pointed-circuit family. -/
def additiveCompositionOfCurrentsClaim5643
    {α V : Type*} [DecidableEq α] [AddCommGroup V]
    (J : Finset α) (v : J → V) : Prop :=
  let j : Finset J → V := fun I => ∑ b ∈ I, v b
  ∀ I₁ I₂ : Finset J,
    Disjoint I₁ I₂ →
    I₁ ∪ I₂ ≠ (Finset.univ : Finset J) →
      j (I₁ ∪ I₂) = j I₁ + j I₂

end MathlibPlus.Open
