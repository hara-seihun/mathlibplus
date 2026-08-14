import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The multiplier-weighted reflection filling equation holds exactly in the
zero-multiplier or half-parameter cases under the stated reflection and
zero-set hypotheses.
-/
def multiplierWeightedReflectionFillingEquation : Prop :=
  ∀ (m h hR : ℂ) (r : ℝ) (a : ℝ → ℂ),
    (∀ x : ℝ, a x = 0 ↔ x = 0) →
      h = a (2 * r - 1) →
        hR = -h →
          (m * hR = m * h ↔ m = 0 ∨ r = 1 / 2)

end MathlibPlus.Open.Analysis
