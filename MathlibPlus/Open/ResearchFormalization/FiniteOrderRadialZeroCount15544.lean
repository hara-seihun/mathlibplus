import Mathlib
import MathlibPlus.Open.Analysis.Claim11235_11240_11241

noncomputable section

open Set Filter
open scoped BigOperators ENNReal Topology

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- The analytic multiplicity used for each zero of an entire function. -/
noncomputable def radialZeroMultiplicity (M : ℂ → ℂ) (z : ℂ) : ℕ :=
  analyticOrderNatAt M z

/-- The finite-order zero at the origin, when the origin lies in the disk. -/
noncomputable def originZeroMultiplicity (M : ℂ → ℂ) (R : ℝ) : ℕ :=
  if 0 ≤ R ∧ M 0 = 0 then radialZeroMultiplicity M 0 else 0

/-- Nonzero zeros in a closed disk, represented once for every multiplicity slot. -/
noncomputable def nonzeroRadialZeroCount (M : ℂ → ℂ) (R : ℝ) : ℕ :=
  Nat.card {q : ℂ × ℕ //
    q.1 ≠ 0 ∧ ‖q.1‖ ≤ R ∧ M q.1 = 0 ∧
      q.2 < radialZeroMultiplicity M q.1}

/-- The radial zero count, including the origin with its analytic multiplicity. -/
noncomputable def radialZeroCount (M : ℂ → ℂ) (R : ℝ) : ℕ :=
  originZeroMultiplicity M R + nonzeroRadialZeroCount M R

/-- The classical finite-order exponent, with the maximum-modulus order as its carrier. -/
def hasFiniteOrderExponent (M : ℂ → ℂ) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧
    MathlibPlus.Open.Analysis.entireOrder M = ENNReal.ofReal ρ

/-- The eventual radial growth bound at the exact order `ρ`. -/
def hasExactRadialGrowth (M : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 < R₀ ∧
    ∀ R : ℝ, R₀ ≤ R →
      Real.log ((MathlibPlus.Open.Analysis.maximumModulus M R).toReal) ≤
        C * Real.rpow R ρ

/-- Big-O notation for the real-valued radial zero count. -/
def radialZeroCountIsBigO
    (M : ℂ → ℂ) (α : ℝ) : Prop :=
  Asymptotics.IsBigO atTop
    (fun R : ℝ => (radialZeroCount M R : ℝ))
    (fun R : ℝ => Real.rpow R α)

/-- Claim 15544: finite-order entire functions have polynomial radial zero count,
with analytic multiplicity and the stronger exact-order growth consequence. -/
def finiteOrderEntireRadialZeroCount : Prop :=
  ∀ (M : ℂ → ℂ) (ρ : ℝ),
    Differentiable ℂ M →
      (∃ z : ℂ, M z ≠ 0) →
        hasFiniteOrderExponent M ρ →
          (∀ ε : ℝ, 0 < ε →
            radialZeroCountIsBigO M (ρ + ε)) ∧
          (hasExactRadialGrowth M ρ →
            radialZeroCountIsBigO M ρ)

end MathlibPlus.Open.ResearchFormalization.Batch
