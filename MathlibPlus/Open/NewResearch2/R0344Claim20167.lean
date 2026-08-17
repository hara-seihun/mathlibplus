import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0344

noncomputable section
open scoped BigOperators

/-- The formal multivariate polynomial carrying the finite coefficient residual
of the logarithmic-frequency sum. -/
def residualPolynomial (P R : ℕ) (q : ℕ → ℝ) :
    MvPolynomial ℕ ℝ :=
  Finset.sum (Finset.Icc 2 (P * R)) (fun k =>
    MvPolynomial.monomial (Nat.factorization k) (q k))

/-- A selected prime lies in `(R/2,R]`, with the division-free lower bound. -/
def selectedPrime (R p : ℕ) : Prop :=
  Nat.Prime p ∧ R < 2 * p ∧ p ≤ R

/-- The monomial frequency carried by an eight-subset. -/
def eightSubsetFrequency (U : ℝ) (S : Finset ℕ) : ℝ :=
  U * Real.log ((S.prod id : ℕ) : ℝ)

/-- Claim 20167: the exact eighth-power coefficient at the product of any
selected eight-prime set is the nonzero `8!` product, and distinct sets give
distinct nonzero logarithmic-frequency modes. -/
def exactEightPrimeCoefficient20167 : Prop :=
  ∀ (P R : ℕ) (t U : ℝ) (q : ℕ → ℝ),
    0 < P → 0 < R → 4 * P < R → 0 < U →
    q 1 = 0 →
    (∀ p : ℕ, selectedPrime R p →
      q p = Real.exp ((t / 4) * Real.log (p : ℝ) ^ 2) ∧ q p ≠ 0) →
    ∀ S : Finset ℕ,
      (∀ p ∈ S, selectedPrime R p) → S.card = 8 →
      let K_S : ℕ := S.prod id
      let Q : MvPolynomial ℕ ℝ := residualPolynomial P R q
      MvPolynomial.coeff (Nat.factorization K_S) (Q ^ 8) =
          (Nat.factorial 8 : ℝ) * Finset.prod S (fun p => q p) ∧
        MvPolynomial.coeff (Nat.factorization K_S) (Q ^ 8) ≠ 0 ∧
        0 < K_S ∧ eightSubsetFrequency U S ≠ 0 ∧
        (∀ T : Finset ℕ,
          (∀ p ∈ T, selectedPrime R p) → T.card = 8 →
            S ≠ T → eightSubsetFrequency U S ≠ eightSubsetFrequency U T)

end

end MathlibPlus.Open.NewResearch2.R0344
