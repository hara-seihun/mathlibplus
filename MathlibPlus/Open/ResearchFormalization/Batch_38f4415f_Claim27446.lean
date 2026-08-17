import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27446

private abbrev BooleanRank (m r : ℕ) :=
  {A : Finset (Fin m) // A.card = r}

private def booleanUp (m c : ℕ) :
    (BooleanRank m c → ℚ) → BooleanRank m (c + 1) → ℚ :=
  fun z B =>
    ∑ A : BooleanRank m c,
      if A.1 ⊆ B.1 ∧ A.1 ≠ B.1 then z A else 0

/-- The exact Boolean-up injectivity threshold and its consequence for the
    remaining u≤t strata under the cherry expansion bound. -/
def claim27446 : Prop :=
  ∀ (m c t : ℕ),
    m = c + t →
    (Function.Injective (booleanUp m c) ↔
        (c : ℚ) < (m : ℚ) / 2) ∧
      ((c : ℚ) < (m : ℚ) / 2 ↔ c < t) ∧
      ∀ u : ℕ, 0 < t → u ≤ t → 2 * c ≤ u →
        c ≤ u / 2 ∧ u / 2 ≤ t / 2 ∧ t / 2 < t ∧
          c < t ∧ Function.Injective (booleanUp m c)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27446
