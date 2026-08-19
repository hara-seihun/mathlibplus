import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

open scoped BigOperators

noncomputable section

/-- Claim 711: the sharp same-range coefficient for the weighted prime sum. -/
def sharpSameRangeUpperCoefficient : Prop :=
  let weightedPrimeSum : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)
  let bThree : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        Real.log (p.1 : ℝ) /
          ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
  let normalizedUpperError : ℝ → ℝ := fun x =>
    Real.log x * (weightedPrimeSum x - Real.log x + bThree)
  let cUp : ℝ := normalizedUpperError 467
  (∀ x : ℝ, (319 : ℝ) ≤ x →
      weightedPrimeSum x ≤
          Real.log x - bThree + cUp / Real.log x ∧
        (weightedPrimeSum x =
            Real.log x - bThree + cUp / Real.log x ↔
          x = 467)) ∧
    IsLeast
      {c : ℝ | ∀ x : ℝ, (319 : ℝ) ≤ x →
        weightedPrimeSum x ≤ Real.log x - bThree + c / Real.log x}
      cUp

/-- Claim 712: the sharp coefficient's displayed decimal enclosure and its
strict rational consequences. -/
def sharpUpperCoefficientEnclosure : Prop :=
  let weightedPrimeSum : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)
  let bThree : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        Real.log (p.1 : ℝ) /
          ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
  let normalizedUpperError : ℝ → ℝ := fun x =>
    Real.log x * (weightedPrimeSum x - Real.log x + bThree)
  let cUp : ℝ := normalizedUpperError 467
  let displayedLower : ℝ :=
    49220638285988736762169768962195485662212462650 /
      (10 : ℝ) ^ (47 : ℕ)
  let displayedUpper : ℝ :=
    49220638285988736762169768962195485662212462651 /
      (10 : ℝ) ^ (47 : ℕ)
  displayedLower ≤ cUp ∧
    cUp < displayedUpper ∧
    cUp < (1 / 2 : ℝ) ∧
    cUp < (492207 : ℝ) / 1000000

/-- Claim 713: the strict rounded upper bound on the same range. -/
def strictRoundedUpperBound : Prop :=
  let weightedPrimeSum : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)
  let bThree : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        Real.log (p.1 : ℝ) /
          ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
  ∀ x : ℝ, (319 : ℝ) ≤ x →
    weightedPrimeSum x <
      Real.log x - bThree + ((492207 : ℝ) / 1000000) / Real.log x

/-- Claim 714: the global lower coefficient, its displayed decimal enclosure,
and the rational corollary. -/
def globalLowerCoefficient : Prop :=
  let weightedPrimeSum : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)
  let bThree : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        Real.log (p.1 : ℝ) /
          ((p.1 : ℝ) * ((p.1 : ℝ) - 1))
  let logarithmAtLimit : ℝ := Real.log ((10 : ℝ) ^ 8)
  let cLow : ℝ :=
    3 / (40 * logarithmAtLimit) +
      3 / (20 * logarithmAtLimit ^ 2)
  let displayedLower : ℝ :=
    45135694327139560308386168100737840691644 /
      (10 : ℝ) ^ (43 : ℕ)
  let displayedUpper : ℝ :=
    45135694327139560308386168100737840691645 /
      (10 : ℝ) ^ (43 : ℕ)
  (∀ x : ℝ, 1 < x →
      weightedPrimeSum x >
          Real.log x - bThree - cLow / Real.log x ∧
        Real.log x - bThree - cLow / Real.log x >
          Real.log x - bThree - 1 / ((221 : ℝ) * Real.log x)) ∧
    displayedLower ≤ cLow ∧
    cLow < displayedUpper ∧
    cLow < (1 : ℝ) / 221

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
