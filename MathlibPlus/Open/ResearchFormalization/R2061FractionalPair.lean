import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2061FractionalPair

/-- The finite fractional pair-product inequality, with the unordered pair
sum written inline so no standalone helper definition is needed. -/
def claim35935 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℝ),
    (∀ i : Fin k, 0 ≤ a i ∧ a i ≤ 1) →
    (∑ i : Fin k, a i) ≤
      1 + ∑ i : Fin k, ∑ j : Fin k,
        if i < j then a i * a j else 0

end MathlibPlus.Open.ResearchFormalization.R2061FractionalPair
