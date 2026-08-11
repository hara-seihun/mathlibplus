import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
Statement-fidelity registry nodes for claims 803 and 805.  Mathlib's
`Chebyshev.theta` is used directly; the numerical constants are exact rationals.
-/

/-- Claim 803: the published infinite-tail Chebyshev-theta envelope. -/
def publishedInfiniteTailThetaBound : Prop :=
  ∀ x : ℝ, (5000000 : ℝ) < x →
    |Chebyshev.theta x - x| ≤ 58 * x / (Real.log x) ^ (4 : ℕ)

/-- Claim 805: the strict rounded coefficient on the range `x ≥ 70111`,
including the three reported margins relative to the exact coefficient from
claim 804. -/
def convenientStrictThetaCoefficient : Prop :=
  let cStar : ℝ :=
    ((70117 : ℝ) - Chebyshev.theta 70111) *
      (Real.log 70117) ^ (4 : ℕ) / 70117
  (∀ x : ℝ, (70111 : ℝ) ≤ x →
    |Chebyshev.theta x - x| <
      (99226 / 1000 : ℝ) * x / (Real.log x) ^ (4 : ℕ)) ∧
    (99226 / 1000 : ℝ) - cStar > 836 / 1000000 ∧
    100 - cStar > 774 / 1000 ∧
    cStar - 58 > 41225 / 1000

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/-!
Statement-fidelity registry nodes for claims 810 and 811.  The normalized
psi error is inlined as `|(Chebyshev.psi x - x) / x|`, and the source's
`R = 5.5666305` and displayed decimals are represented by exact rationals.
-/

/-- Claim 810: the global normalized Chebyshev-psi envelope. -/
def globalPsiNormalizedEnvelope : Prop :=
  let R : ℝ := 55666305 / 10000000
  ∀ x : ℝ, 2 < x →
    |(Chebyshev.psi x - x) / x| ≤
      (121096 / 1000 : ℝ) *
        Real.rpow (Real.log x / R) (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (Real.log x / R))

/-- Claim 811: exact de-normalization and the directed constant certificate. -/
def exactPsiEnvelopeDenormalization : Prop :=
  let R : ℝ := 55666305 / 10000000
  let cStar : ℝ := (121096 / 1000 : ℝ) / Real.rpow R (3 / 2 : ℝ)
  let dStar : ℝ := 2 / Real.sqrt R
  (∀ x : ℝ, 2 < x →
    |(Chebyshev.psi x - x) / x| ≤
      cStar * Real.rpow (Real.log x) (3 / 2 : ℝ) *
        Real.exp (-dStar * Real.sqrt (Real.log x))) ∧
    (92202183441759598 / 10000000000000000 : ℝ) ≤ cStar ∧
    cStar < (92202183441759599 / 10000000000000000 : ℝ) ∧
    (8476836336683192 / 10000000000000000 : ℝ) ≤ dStar ∧
    dStar < (8476836336683193 / 10000000000000000 : ℝ) ∧
    dStar - (8476836 / 10000000 : ℝ) >
      (33668 / 1000000000000 : ℝ)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
