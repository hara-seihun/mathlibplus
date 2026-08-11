import Mathlib

/-!
# A4 coefficient scaling

The exact eight-term limiting profile is proved algebraically. The analytic coefficient
scaling and its local discrete-`C²` strengthening are retained as an open registry node.
-/

namespace MathlibPlus.Analysis.A4CoefficientScaling

/-- The eight pole contributions in claim 315 sum to four times its Binet continuum
profile. -/
theorem eightPoleContributions_sum (z : ℝ) :
    1 + 0 + 4 * z * Real.exp z - Real.exp (-z) +
        2 * z * Real.exp (-z) - (4 / 3 : ℝ) * z ^ 2 * Real.exp (-z) +
        0 + (16 / 45 : ℝ) * z ^ 4 * Real.exp (-z) =
      4 * ((1 / 4 : ℝ) + z * Real.exp z +
        Real.exp (-z) *
          ((4 / 45 : ℝ) * z ^ 4 - (1 / 3 : ℝ) * z ^ 2 +
            (1 / 2 : ℝ) * z - 1 / 4)) := by
  ring

end MathlibPlus.Analysis.A4CoefficientScaling

namespace MathlibPlus.Open.Analysis.A4CoefficientScaling

/-- Claim 315: Taylor coefficients of the exact A4 Cayley generating function converge
locally uniformly to `4b`; their first differences and `r`-scaled second differences
converge locally uniformly to the first two derivatives of `4b`.

The coefficient at index `m` is made canonical as `Φ_r^(m)(0)/m!`. For the source's
phrase "local `C²` form", first and second discrete derivatives use respectively
`Δφ_m` and `r Δ²φ_m`, the scalings forced by `r⁻¹ φ_{⌊rz⌋}` on mesh `1/r`. -/
noncomputable def coefficientScalingLaw : Prop :=
  let b : ℝ → ℝ := fun z =>
    (1 / 4 : ℝ) + z * Real.exp z +
      Real.exp (-z) *
        ((4 / 45 : ℝ) * z ^ 4 - (1 / 3 : ℝ) * z ^ 2 +
          (1 / 2 : ℝ) * z - 1 / 4)
  let aPrime : ℝ → ℝ := fun v =>
    (15 * v ^ 6 + 416 * v ^ 5 + 236 * v ^ 4 + 5504 * v ^ 3 +
        8400 * v ^ 2 + 10240 * v + 6720) /
      (30 * (v - 2) ^ 2 * (v + 2) ^ 5)
  let cayley : ℝ → ℝ := fun s => (1 + s) / (1 - s)
  let Φ : ℝ → ℝ → ℝ := fun r s => cayley s ^ 2 * aPrime (cayley s / r)
  let φ : ℝ → ℕ → ℝ := fun r m =>
    iteratedDeriv m (Φ r) 0 / (m.factorial : ℝ)
  let index : ℝ → ℝ → ℕ := fun r z => ⌊r * z⌋₊
  (∀ (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ z : ℝ, z ∈ Set.Icc 0 A →
        |r⁻¹ * φ r (index r z) - 4 * b z| < ε) ∧
  (∀ (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ z : ℝ, z ∈ Set.Icc 0 A →
        |(φ r (index r z + 1) - φ r (index r z)) - 4 * deriv b z| < ε) ∧
  (∀ (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ z : ℝ, z ∈ Set.Icc 0 A →
        |r * (φ r (index r z + 2) - 2 * φ r (index r z + 1) +
              φ r (index r z)) -
          4 * iteratedDeriv 2 b z| < ε) ∧
  ∀ z : ℝ,
    1 + 0 + 4 * z * Real.exp z - Real.exp (-z) +
        2 * z * Real.exp (-z) - (4 / 3 : ℝ) * z ^ 2 * Real.exp (-z) +
        0 + (16 / 45 : ℝ) * z ^ 4 * Real.exp (-z) = 4 * b z

end MathlibPlus.Open.Analysis.A4CoefficientScaling
