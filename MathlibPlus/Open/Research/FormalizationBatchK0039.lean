import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

open scoped BigOperators

/-- The `r`-th term in the matrix logarithm power series, with the constant
term removed. -/
def matrixLogTerm {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  if 1 ≤ r then
    (((-1 : ℂ) ^ (r + 1)) / (r : ℂ)) • ((Z - 1) ^ r)
  else 0

/-- The logarithm power series used by the incidence calculation. -/
def matrixLogSeries {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑' r : ℕ, matrixLogTerm Z r

/-- Claim 7048: nilpotence makes the logarithm power series an exact finite
sum. -/
def claim7048ExactFiniteIncidenceLog : Prop :=
  ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) (m : ℕ),
    (Z - 1) ^ m = 0 →
      matrixLogSeries Z = ∑ r ∈ Finset.range m, matrixLogTerm Z r

/-- A finite set of natural numbers is divisor-closed. -/
def divisorClosed (s : Finset ℕ) : Prop :=
  ∀ ⦃d n : ℕ⦄, n ∈ s → d ∣ n → d ∈ s

/-- The divisibility incidence matrix on a finite divisor-closed set. -/
def divisorZeta (s : Finset ℕ) :
    Matrix {n // n ∈ s} {n // n ∈ s} ℂ :=
  fun d n => if (d : ℕ) ∣ (n : ℕ) then 1 else 0

/-- The logarithm terms for the finite divisibility incidence matrix. -/
def divisorLogTerm (s : Finset ℕ) (r : ℕ) :
    Matrix {n // n ∈ s} {n // n ∈ s} ℂ :=
  if 1 ≤ r then
    (((-1 : ℂ) ^ (r + 1)) / (r : ℂ)) • ((divisorZeta s - 1) ^ r)
  else 0

/-- The incidence logarithm on a finite divisor-closed set. -/
def divisorLogSeries (s : Finset ℕ) :
    Matrix {n // n ∈ s} {n // n ∈ s} ℂ :=
  ∑' r : ℕ, divisorLogTerm s r

/-- The coefficient contributed by the prime-power quotients.  The finite
sum avoids choosing a representation of a prime power. -/
def primePowerCoefficient (q : ℕ) : ℂ :=
  ∑ p ∈ Finset.range (q + 1),
    ∑ k ∈ Finset.range (q + 1),
      if Nat.Prime p ∧ 1 ≤ k ∧ q = p ^ k then 1 / (k : ℂ) else 0

/-- Having at least two distinct prime divisors. -/
def hasTwoDistinctPrimeFactors (q : ℕ) : Prop :=
  ∃ p r : ℕ,
    Nat.Prime p ∧ Nat.Prime r ∧ p ≠ r ∧ p ∣ q ∧ r ∣ q

/-- The prime-power support formula on one finite divisor-closed set. -/
def primePowerSupportOn (s : Finset ℕ) : Prop :=
  ∀ (d n : ℕ) (hd : d ∈ s) (hn : n ∈ s),
    d ∣ n →
      divisorLogSeries s ⟨d, hd⟩ ⟨n, hn⟩ = primePowerCoefficient (n / d)

/-- The explicit test set from Claim 7049. -/
def claim7049TestSet : Finset ℕ := {1, 2, 3, 4, 6, 8, 9, 12}

/-- Claim 7049: the finite incidence logarithm has only prime-power support,
with exact mixed-prime cancellation, including the stated test ratios. -/
def claim7049PrimePowerSupport : Prop :=
  (∀ (s : Finset ℕ), divisorClosed s → primePowerSupportOn s) ∧
    (∀ (s : Finset ℕ), divisorClosed s →
      ∀ (d n : ℕ) (hd : d ∈ s) (hn : n ∈ s), d ∣ n →
        hasTwoDistinctPrimeFactors (n / d) →
          divisorLogSeries s ⟨d, hd⟩ ⟨n, hn⟩ = 0) ∧
    divisorClosed claim7049TestSet ∧
    divisorLogSeries claim7049TestSet
        ⟨1, by simp [claim7049TestSet]⟩
        ⟨6, by simp [claim7049TestSet]⟩ = 0 ∧
    divisorLogSeries claim7049TestSet
        ⟨1, by simp [claim7049TestSet]⟩
        ⟨12, by simp [claim7049TestSet]⟩ = 0

end

end MathlibPlus.Open.Research
