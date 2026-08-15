import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.NumberTheory.FormalizationBatch

/-- The real-valued Möbius coefficient used in the admitted divisor sums. -/
def mobiusReal (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℤ)

/-- Real powers of positive integer bases, with the ambient real-power convention. -/
def natRealPow (n : ℕ) (s : ℝ) : ℝ := (n : ℝ) ^ s

/-- The least-residue carrier from the admitted arithmetic statements. -/
def leastResidue (N k : ℕ) : ℕ := k % N

/-- The real Riemann zeta value at a real argument. -/
def realZeta (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re

/-- The generalized Jordan coefficient with the prime q omitted. -/
def generalizedJordanCoefficient (q : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ (Nat.primeFactors n).filter (fun p => p ≠ q),
    (1 - natRealPow p (-t))

/-- The outer Dirichlet series in Claim 8216. -/
def outerResidueSeries (k : ℕ) (z : ℝ) : ℝ :=
  ∑' N : ℕ,
    if 1 < N ∧ Nat.Coprime N k then
      mobiusReal N * (leastResidue N k : ℝ) / natRealPow N z
    else 0

/-- The prime product occurring in the first term of Claim 8216. -/
def outerPrimeProduct (k : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ Nat.primeFactors k, (1 - natRealPow p (-z))⁻¹

/-- The finite divisor correction occurring in Claim 8216. -/
def outerFiniteCorrection (k : ℕ) (z : ℝ) : ℝ :=
  ∑ N ∈ (Finset.Icc 1 k).filter (fun N => Nat.Coprime N k),
    mobiusReal N * ((k / N : ℕ) : ℝ) * natRealPow N (1 - z)

/-- Claim 8216: the exact outer packet formula for z>1. -/
def claim8216_outer_packet_formula : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∀ z : ℝ, 1 < z →
      outerResidueSeries k z =
        (k : ℝ) / realZeta z * outerPrimeProduct k z - outerFiniteCorrection k z

/-- The Möbius divisor sum in Claim 8249. -/
def divisorMobiusSum (q j : ℕ) (t : ℝ) : ℝ :=
  ∑ N ∈ (Nat.divisors j).filter (fun N => ¬ q ∣ N),
    mobiusReal N / natRealPow N t

/-- Claim 8249: the divisor-product identity. -/
def claim8249_divisor_product_identity : Prop :=
  ∀ q : ℕ, Nat.Prime q →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∀ j : ℕ, 1 ≤ j →
        divisorMobiusSum q j t =
          generalizedJordanCoefficient q t j

end MathlibPlus.Open.NumberTheory.FormalizationBatch
