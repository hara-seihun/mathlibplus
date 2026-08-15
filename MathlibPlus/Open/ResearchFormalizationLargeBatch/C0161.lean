import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim2493_compactEndpointTransform : Prop := by
  exact ∀ (a A L : ℝ) (k : ℝ → ℝ),
    0 < a → a < A → ContDiff ℝ ⊤ k →
    IsCompact (Function.support k) → Function.support k ⊆ Set.Ioo a A →
    ∃! T : ℂ → ℂ, ∀ z,
      T z = ∫ x in a..A,
        (k x : ℂ) * Complex.cos (z * ((x - L / 2 : ℝ) : ℂ))

end MathlibPlus.Open.ResearchFormalizationLargeBatch
