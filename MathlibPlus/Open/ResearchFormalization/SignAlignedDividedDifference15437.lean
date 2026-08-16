import Mathlib

open scoped BigOperators Topology
open MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.SignAlignedDividedDifference15437

noncomputable section

/-- The horizontal point `x + i y` used by the endpoint-band transform. -/
def horizontalPoint (x y : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (y : ℂ)

/-- The endpoint-band Fourier--Laplace carrier from the same source group. -/
noncomputable def endpointBandTransform
    (μ : MeasureTheory.ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  ∫ᵛ τ : ℝ,
    Complex.exp (Complex.I * (τ : ℂ) * z)
    ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- The real barycentric denominator `∏_{k ≠ j} (x_j - x_k)`. -/
def barycentricDenominator {n : ℕ}
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  ∏ k ∈ (Finset.univ.erase j), (x j - x k)

/-- The ordinary barycentric formula for the divided difference. -/
noncomputable def ordinaryDividedDifference {n : ℕ}
    (B : ℝ → ℂ) (x : Fin (n + 1) → ℝ) : ℂ :=
  ∑ j : Fin (n + 1),
    B (x j) / (barycentricDenominator x j : ℂ)

/-- Successive half-turn values lie on one common complex line, alternate in
sign, and have the stated trace minimum. -/
def alternatingEndpointValues {n : ℕ}
    (μ : MeasureTheory.ComplexMeasure ℝ)
    (x : Fin (n + 1) → ℝ) (y aStar : ℝ) : Prop :=
  ∃ (u : ℂ) (c : Fin (n + 1) → ℝ),
    ‖u‖ = 1 ∧
      ∀ j : Fin (n + 1),
        endpointBandTransform μ (horizontalPoint (x j) y) =
            (c j : ℂ) * u ∧
          ((-1 : ℝ) ^ (j : ℕ)) * c j ≥ aStar ∧
          aStar ≤ ‖endpointBandTransform μ (horizontalPoint (x j) y)‖

/-- Claim 15437: for increasing nodes on an interval of length `S`, the
real barycentric denominators have signs `(-1)^(n-j)`; successive half-turn
values on one common line then give the stated divided-difference lower bound. -/
def signAlignedDividedDifferenceLowerBound_claim15437 : Prop :=
  ∀ (n : ℕ) (r y S aStar : ℝ)
    (μ : MeasureTheory.ComplexMeasure ℝ)
    (x : Fin (n + 1) → ℝ),
    0 ≤ r →
    0 < S →
    0 ≤ aStar →
    IsFiniteMeasure μ.variation →
    μ.variation (Set.Icc (-r) 0)ᶜ = 0 →
    StrictMono x →
    x (Fin.last n) - x 0 ≤ S →
    alternatingEndpointValues μ x y aStar →
    let d : Fin (n + 1) → ℝ :=
      fun j => barycentricDenominator x j
    (∀ j : Fin (n + 1),
      0 < ((-1 : ℝ) ^ (n - (j : ℕ))) * d j) ∧
      ‖ordinaryDividedDifference
          (fun t : ℝ => endpointBandTransform μ (horizontalPoint t y)) x‖ ≥
        ((n + 1 : ℕ) : ℝ) * aStar / S ^ n

end

end MathlibPlus.Open.ResearchFormalization.SignAlignedDividedDifference15437
