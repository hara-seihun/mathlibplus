import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0052b_1696_7424_8955_6ad643cbba3f

open scoped BigOperators
open Set

namespace MathlibPlus.Open.ResearchFormalization.K0005

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a0052b_1696_7424_8955_6ad643cbba3f

/-- The one-dimensional action of the five-dimensional radial Laplacian on a
positive-radius test function, obtained by applying the flux pairing to
`r⁻⁴ φ`. -/
def radialLaplacianPairing (φ : ℝ → ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ),
    fiveDimensionalNewtonPotential r *
      derivWithin
        (fun s : ℝ => s ^ 4 *
          derivWithin (fun t : ℝ => (t ^ 4)⁻¹ * φ t)
            (Ioi (0 : ℝ)) s)
        (Ioi (0 : ℝ)) r

/-- Pairing of the bulk term `-2r⁻⁴` with a test function. -/
def bulkRadialPairing (φ : ℝ → ℝ) : ℝ :=
  (-2 : ℝ) * ∫ r in Ioi (0 : ℝ), (r ^ 4)⁻¹ * φ r

/-- The one-dimensional action of `δ_n`. -/
def deltaAction (n : {n : ℕ // 1 ≤ n}) (φ : ℝ → ℝ) : ℝ :=
  φ (n.1 : ℝ)

/-- The one-dimensional action of `δ'_n`, with the sign convention
`δ'_n(φ) = -φ'(n)`. -/
def deltaPrimeAction (n : {n : ℕ // 1 ≤ n}) (φ : ℝ → ℝ) : ℝ :=
  -derivWithin φ (Ioi (0 : ℝ)) (n.1 : ℝ)

/-- The shell part of the target distribution, including the exact powers and
signs from `-∑ (n⁻⁴ δ_n + n⁻³ δ'_n)`. -/
def shellRadialPairing (φ : ℝ → ℝ) : ℝ :=
  ∑' n : {n : ℕ // 1 ≤ n},
    (-((n.1 : ℝ) ^ 4)⁻¹ * deltaAction n φ -
      ((n.1 : ℝ) ^ 3)⁻¹ * deltaPrimeAction n φ)

/-- Claim 6821: the full radial-Laplacian shell formula, expressed by its
canonical action on every smooth compactly supported positive-radius test
function. -/
def claim6821 : Prop :=
  ∀ φ : ℝ → ℝ,
    radialTestFunction φ →
      radialLaplacianPairing φ =
        bulkRadialPairing φ + shellRadialPairing φ

end
end MathlibPlus.Open.ResearchFormalization.K0005
