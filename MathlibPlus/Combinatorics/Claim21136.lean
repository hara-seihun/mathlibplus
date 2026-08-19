import Mathlib

namespace MathlibPlus.Combinatorics.R0414

/-- Claim 21136: an injective conditioned code cannot have more source
members than the product of its coordinate capacities. -/
def generalConditionedCodeProductCapacity_claim21136 : Prop :=
  ∀ (α ι : Type*) [Fintype ι]
    (s : Finset α) (r : ι → ℕ)
    (code : α → (i : ι) → Fin (r i)),
    Set.InjOn code (↑s : Set α) →
      s.card ≤ ∏ i, r i

end MathlibPlus.Combinatorics.R0414
