import Mathlib
import MathlibPlus.NumberTheory.Claim9769
import MathlibPlus.Open.NumberTheory.Claim9764
import MathlibPlus.Open.NumberTheory.Claim9770

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.Claim9771

noncomputable section

/-- The admitted positive-natural cutoff sum `B(x)`. -/
private def B (x : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 x,
    MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff n

/-- The admitted integer Mertens sum on the same natural cutoff. -/
private def M (x : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.moebius n

/-- An eventual power bound on the natural cutoffs, with the carrier kept
explicit rather than replacing the cutoff functions by arbitrary real
functions. -/
private def hasPowerBoundB (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
      |(B x : ℝ)| ≤ C * Real.rpow (x : ℝ) θ

private def hasPowerBoundM (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
      |(M x : ℝ)| ≤ C * Real.rpow (x : ℝ) θ

/-- Claim 9771: every fixed positive power exponent gives equivalent
natural-cutoff bounds for the Farey coefficient sum and Mertens sum.  The
identities in Claims 9769 and 9770 are the two harmonic directions; their
coefficient cost is the convergent factor with exponent `1 + θ`. -/
def powerExponentEquivalence_claim9771 : Prop :=
  ∀ θ : ℝ, 0 < θ →
    hasPowerBoundB θ ↔ hasPowerBoundM θ

end

end MathlibPlus.Open.NumberTheory.Claim9771
