import Mathlib

open Filter
open scoped ENNReal Topology

namespace MathlibPlus.Open.ResearchFormalization.O0329TopologicalSharpness

noncomputable section

/-- The concrete real Hilbert carrier `ℓ²(ℕ)`. -/
abbrev HilbertL2 := lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞)

/-- The standard coordinate vector. -/
noncomputable def standardBasisVector (j : ℕ) : HilbertL2 :=
  lp.single (2 : ℝ≥0∞) j (1 : ℝ)

/-- The concrete coordinate rank-one observer `P_j`. -/
noncomputable def coordinateProjection (j : ℕ) : HilbertL2 →L[ℝ] HilbertL2 :=
  (innerSL ℝ (standardBasisVector j)).smulRight (standardBasisVector j)

/-- Claim 15506: the explicit coordinate observers are compact rank-one
orthogonal projections, converge strongly and weakly to zero (and hence are
sequentially compact in those pointwise operator senses), retain the moving
signal on the weakly-null unit basis, and remain one-separated in operator norm.
This is the concrete sharpness counterexample, not an abstract observer class. -/
def claim15506_topologicallySharpPacking : Prop :=
  (∀ j : ℕ,
      ‖standardBasisVector j‖ = 1 ∧
        Module.finrank ℝ
            (LinearMap.range ((coordinateProjection j).toLinearMap)) = 1 ∧
        IsCompact
          (coordinateProjection j '' Metric.closedBall (0 : HilbertL2) 1) ∧
        (∀ x : HilbertL2,
          coordinateProjection j (coordinateProjection j x) =
            coordinateProjection j x) ∧
        (∀ x y : HilbertL2,
          inner ℝ (coordinateProjection j x) y =
            inner ℝ x (coordinateProjection j y))) ∧
    (∀ x : HilbertL2,
      Filter.Tendsto (fun j : ℕ => coordinateProjection j x)
        Filter.atTop (𝓝 0)) ∧
    (∀ x y : HilbertL2,
      Filter.Tendsto
        (fun j : ℕ => inner ℝ (coordinateProjection j x) y)
        Filter.atTop (𝓝 0)) ∧
    (∀ x : HilbertL2,
      Filter.Tendsto
        (fun j : ℕ => inner ℝ x (standardBasisVector j))
        Filter.atTop (𝓝 0)) ∧
    (∀ j : ℕ,
      coordinateProjection j (standardBasisVector j) =
          standardBasisVector j ∧
        ‖coordinateProjection j (standardBasisVector j)‖ = 1) ∧
    (∀ i j : ℕ, i ≠ j →
      ‖coordinateProjection i - coordinateProjection j‖ = 1)

end

end MathlibPlus.Open.ResearchFormalization.O0329TopologicalSharpness
