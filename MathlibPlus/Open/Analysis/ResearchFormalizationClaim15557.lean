import Mathlib
import MathlibPlus.Analysis.ClaimDefinitions20260811

open scoped BigOperators
open Filter MeasureTheory Set Classical

namespace MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557

noncomputable section

/-- The open right half-plane on which the `H∞` multiplier is holomorphic. -/
def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

/-- The real-valued restriction of a complex multiplier on the positive axis. -/
def multiplierRealPart (M : ℂ → ℂ) (t : ℝ) : ℝ :=
  (M (t : ℂ)).re

/-- The archimedean density in the exact mixed carrier. -/
def completedMixedDensity (M : ℂ → ℂ) (t : ℝ) : ℝ :=
  MathlibPlus.Analysis.Claim15541.completedArchimedeanDensity t *
    multiplierRealPart M t

/-- The exact von Mangoldt atom weight in the mixed carrier. -/
def completedMixedAtom (M : ℂ → ℂ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (n : ℝ) *
    multiplierRealPart M (Real.log (n : ℝ))

/-- The value on a compact set of the exact mixed carrier
`κ(t) M(t) dt + ∑_{n≥2} Λ(n) log(n) M(log(n)) δ_(log n)`.
The continuous term is restricted to the positive half-line, as in the
Laplace-carrier representation; the endpoint has zero Lebesgue measure. -/
noncomputable def completedMixedCarrierValue
    (M : ℂ → ℂ) (K : Set ℝ) : ℝ :=
  (∫ t in K ∩ Set.Ioi (0 : ℝ), completedMixedDensity M t ∂volume) +
    ∑' n : {n : ℕ // 2 ≤ n},
      if Real.log (n.1 : ℝ) ∈ K then completedMixedAtom M n.1 else 0

/-- A nonnegative locally finite measure realizing the exact signed carrier.
The compact-set equations retain the signed density and every atomic term;
nonnegativity is expressed by the existence of the measure rather than by
replacing the carrier with pointwise helper predicates. -/
def exactCompletedMixedCarrier
    (M : ℂ → ℂ) (ν : Measure ℝ) : Prop :=
  IsLocallyFiniteMeasure ν ∧
    ∀ K : Set ℝ, IsCompact K →
      0 ≤ completedMixedCarrierValue M K ∧
        ν K = ENNReal.ofReal (completedMixedCarrierValue M K)

/-- Claim 15557: a bounded holomorphic right-half-plane multiplier, real on
`(0,∞)`, cannot produce a nonnegative locally finite exact completed mixed
carrier unless it vanishes on the right half-plane. -/
def boundedHalfPlaneMultiplierZero_claim15557 : Prop :=
  ∀ M : ℂ → ℂ,
    (DifferentiableOn ℂ M rightHalfPlane ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ∈ rightHalfPlane → ‖M z‖ ≤ C) →
    (∀ t : ℝ, 0 < t → (M (t : ℂ)).im = 0) →
    (∃ ν : Measure ℝ, exactCompletedMixedCarrier M ν) →
    ∀ z : ℂ, z ∈ rightHalfPlane → M z = 0

end
end MathlibPlus.Open.Analysis.ResearchFormalizationClaim15557
