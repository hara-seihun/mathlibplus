import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0172

open scoped BigOperators
open scoped Topology

/-- Claim 18539: the type-B alternant is the Vandermonde product in the
squared shifted-logarithmic coordinates. -/
def claim18539_typeBAlternantSquaredU : Prop :=
  ∀ r : ℕ, ∀ x : Fin r → ℝ, ∀ T : ℝ,
    0 < T → (∀ i, 0 < x i) →
      let L : ℝ := Real.log (T / Real.pi)
      let U : Fin r → ℝ := fun i => L - 2 * Real.log (x i)
      Matrix.det (fun i j : Fin r => (U i) ^ (2 * j.val)) =
        ∏ i : Fin r, ∏ j : Fin r, if i.val < j.val then
          (U j) ^ 2 - (U i) ^ 2 else 1

end MathlibPlus.Open.NewResearch2.R0172
