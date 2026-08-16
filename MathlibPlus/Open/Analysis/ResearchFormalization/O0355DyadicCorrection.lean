import Mathlib

open scoped BigOperators
open Filter

namespace MathlibPlus.Open.Analysis.ResearchFormalizationO0355

noncomputable section

abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
abbrev PositiveExponent := {k : ℕ // 1 ≤ k}
abbrev PrimePowerIndex := PrimeIndex × PositiveExponent

/-- The real form of the fixed reflected-conjugate quartet's prime correction. -/
noncomputable def quartetPrimeBaseline (α : ℝ) (m : ℕ) (τ : ℝ)
    (p : PrimeIndex) : ℝ :=
  1 - 2 * (m : ℝ) *
    (Real.rpow (p.1 : ℝ) (-α) +
      Real.rpow (p.1 : ℝ) (-(1 - α))) *
    Real.cos (τ * Real.log (p.1 : ℝ))

/-- Add the common correction on the primes in `(Y, 2Y]`, while retaining
exactly the zeta values through `Y`. -/
noncomputable def correctedPrimeValue (α : ℝ) (m : ℕ) (τ Y u : ℝ)
    (p : PrimeIndex) : ℝ :=
  if Y < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * Y then
    quartetPrimeBaseline α m τ p + u
  else if (p.1 : ℝ) ≤ Y then
    1
  else
    quartetPrimeBaseline α m τ p

/-- The summand in the absolutely convergent signed weighted perturbation. -/
noncomputable def dyadicCorrectionSummand (α : ℝ) (m : ℕ) (τ Y u : ℝ)
    (q : PrimePowerIndex) : ℝ :=
  ((correctedPrimeValue α m τ Y u q.1) ^ q.2.1 - 1) *
      Real.log (q.1.1 : ℝ) /
    (q.1.1 : ℝ) ^ q.2.1

/-- The signed weighted perturbation `Δ_Y(u)`. -/
noncomputable def dyadicCorrection (α : ℝ) (m : ℕ) (τ Y u : ℝ) : ℝ :=
  ∑' q : PrimePowerIndex, dyadicCorrectionSummand α m τ Y u q

/-- The derivative sum over the corrected prime interval. -/
noncomputable def dyadicCorrectionDerivative (α : ℝ) (m : ℕ) (τ Y u : ℝ) : ℝ :=
  ∑' p : PrimeIndex,
    if Y < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * Y then
      (p.1 : ℝ) * Real.log (p.1 : ℝ) /
        ((p.1 : ℝ) - correctedPrimeValue α m τ Y u p) ^ 2
    else 0

/-- Claim 15620: the common dyadic correction has a uniformly positive
and uniformly bounded derivative on its natural `O(Y^(-α))` window. -/
noncomputable def dyadicCorrectionHasPositiveDerivative_claim15620 : Prop :=
  ∀ (α τ : ℝ) (m : ℕ),
    0 < α →
    α < (1 / 2 : ℝ) →
    Irrational α →
    0 < τ →
    1 ≤ m →
    ∃ U c C Y₀ : ℝ,
      0 < U ∧
      0 < c ∧
      c ≤ C ∧
      1 ≤ Y₀ ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        ∀ u : ℝ, |u| ≤ U * Real.rpow Y (-α) →
          Summable (fun q : PrimePowerIndex =>
            |dyadicCorrectionSummand α m τ Y u q|) ∧
          HasDerivAt (dyadicCorrection α m τ Y)
            (dyadicCorrectionDerivative α m τ Y u) u ∧
          c ≤ dyadicCorrectionDerivative α m τ Y u ∧
          dyadicCorrectionDerivative α m τ Y u ≤ C

end
end MathlibPlus.Open.Analysis.ResearchFormalizationO0355
