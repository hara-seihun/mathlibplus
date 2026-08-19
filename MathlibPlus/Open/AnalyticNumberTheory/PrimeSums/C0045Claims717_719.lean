import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

open scoped BigOperators

noncomputable section

/-- Claim 717: Dusart's weighted-prime tail estimate and its normalized-error
consequences.  The real cutoff is represented by the primes at most
`Nat.floor x`. -/
def dusartWeightedPrimeTail : Prop :=
  let S : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.Iic (Nat.floor x)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)
  let B₃ : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        Real.log (p.1 : ℝ) /
          ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
  let F : ℝ → ℝ := fun x => Real.log x * (S x - Real.log x + B₃)
  ∀ x : ℝ, 912560 ≤ x →
    |S x - Real.log x + B₃| ≤ (3 / 10 : ℝ) / Real.log x ^ 2 ∧
    F x ≤ (3 / 10 : ℝ) / Real.log x ∧
    (3 / 10 : ℝ) / Real.log x < 11 / 500 ∧
    F x < 1093 / 50000

/-- Claim 718: Rosser--Schoenfeld's finite-range sign theorem for the
weighted prime sum. -/
def finiteRangeSign : Prop :=
  let S : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.Iic (Nat.floor x)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)
  let B₃ : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        Real.log (p.1 : ℝ) /
          ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
  ∀ x : ℝ, 0 < x → x ≤ (10 : ℝ) ^ 8 →
    S x > Real.log x - B₃

/-- Claim 719: Axler's global asymmetric lower estimate for the weighted
prime sum. -/
def globalAxlerLowerEstimate : Prop :=
  let S : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.Iic (Nat.floor x)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)
  let B₃ : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        Real.log (p.1 : ℝ) /
          ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
  ∀ x : ℝ, x > 1 →
    S x - Real.log x + B₃ ≥
      -3 / (40 * Real.log x ^ 2) - 3 / (20 * Real.log x ^ 3)

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
