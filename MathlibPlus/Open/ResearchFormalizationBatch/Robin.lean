import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Robin

open scoped BigOperators

noncomputable section

def divisorSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ)

def robinG (n : ℕ) : ℝ :=
  divisorSum n / ((n : ℝ) * Real.log (Real.log (n : ℝ)))

def epsilon (n : ℕ) : ℝ :=
  1 / (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)))

def primePowerSum (p k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, (p : ℝ) ^ i

def breakpointF (p k : ℕ) : ℝ :=
  Real.log (1 + 1 / primePowerSum p k) / Real.log (p : ℝ)

def etaP (p : ℕ) (y : ℝ) : ℝ :=
  Real.log (Real.log (y + Real.log (p : ℝ)) / Real.log y) /
    Real.log (p : ℝ)

def valuation (p n : ℕ) : ℕ :=
  Nat.factorization n p

def additionMargin (p n : ℕ) : ℝ :=
  etaP p (Real.log (n : ℝ)) - breakpointF p (valuation p n + 1)

def removalMargin (p n : ℕ) : ℝ :=
  breakpointF p (valuation p n) -
    etaP p (Real.log (n : ℝ) - Real.log (p : ℝ))

def claim42923 : Prop :=
  (∀ n : ℕ, Real.exp 1 < (n : ℝ) →
    robinG n = divisorSum n / ((n : ℝ) * Real.log (Real.log (n : ℝ)))) ∧
  (∀ n : ℕ, Real.exp 1 < (n : ℝ) →
    epsilon n = 1 / (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)))) ∧
  (∀ p k : ℕ, Nat.Prime p → 1 ≤ k →
    breakpointF p k =
      Real.log (1 + 1 / (∑ i ∈ Finset.Icc 1 k, (p : ℝ) ^ i)) /
        Real.log (p : ℝ)) ∧
  (∀ p : ℕ, Nat.Prime p → ∀ y : ℝ, 1 < y →
    etaP p y =
      Real.log (Real.log (y + Real.log (p : ℝ)) / Real.log y) /
        Real.log (p : ℝ)) ∧
  (∀ n p : ℕ, Real.exp 1 < (n : ℝ) → Nat.Prime p →
    additionMargin p n =
      etaP p (Real.log (n : ℝ)) - breakpointF p (Nat.factorization n p + 1)) ∧
  (∀ n p : ℕ, Real.exp 1 < (n : ℝ) → Nat.Prime p → p ∣ n →
    removalMargin p n =
      breakpointF p (Nat.factorization n p) -
        etaP p (Real.log (n : ℝ) - Real.log (p : ℝ)))

def additionLogDomain (n p : ℕ) : Prop :=
  0 < Real.log (n : ℝ) ∧
  0 < Real.log (p : ℝ) ∧
  0 < Real.log (Real.log (n : ℝ)) ∧
  0 < Real.log (Real.log ((n * p : ℕ) : ℝ)) ∧
  0 < Real.log (Real.log (n : ℝ) + Real.log (p : ℝ)) ∧
  0 < Real.log (Real.log (n : ℝ) + Real.log (p : ℝ)) /
      Real.log (Real.log (n : ℝ))

def removalLogDomain (n p : ℕ) : Prop :=
  0 < Real.log (n : ℝ) ∧
  0 < Real.log ((n / p : ℕ) : ℝ) ∧
  0 < Real.log (p : ℝ) ∧
  0 < Real.log (Real.log (n : ℝ)) ∧
  0 < Real.log (Real.log ((n / p : ℕ) : ℝ)) ∧
  0 < Real.log (Real.log (n : ℝ) - Real.log (p : ℝ)) ∧
  0 < Real.log (Real.log (n : ℝ)) /
      Real.log (Real.log (n : ℝ) - Real.log (p : ℝ))

def claim42925 : Prop :=
  ∀ (n p : ℕ), Real.exp 1 < (n : ℝ) → Nat.Prime p →
    additionLogDomain n p →
      Real.log (robinG (n * p)) - Real.log (robinG n) =
        Real.log (p : ℝ) *
          (breakpointF p (Nat.factorization n p + 1) -
            etaP p (Real.log (n : ℝ)))

def claim42926 : Prop :=
  ∀ (n p : ℕ), p ∣ n → Nat.Prime p →
    Real.exp 1 < ((n / p : ℕ) : ℝ) → removalLogDomain n p →
      Real.log (robinG n) - Real.log (robinG (n / p)) =
        Real.log (p : ℝ) *
          (breakpointF p (Nat.factorization n p) -
            etaP p (Real.log (n : ℝ) - Real.log (p : ℝ)))

def threshold (p k : ℕ) : ℝ := by
  classical
  exact if h : ∃ t : ℝ, 1 < t ∧ etaP p t = breakpointF p k then
    Classical.choose h
  else
    0

def qBreakpoint (p k : ℕ) : ℝ :=
  Real.exp (Real.log (p : ℝ) * breakpointF p k)

def claim42928 : Prop :=
  ∀ (p k : ℕ), Nat.Prime p → 1 ≤ k →
    (∃! T : ℝ, 1 < T ∧ etaP p T = breakpointF p k) ∧
    threshold p k + Real.log (p : ℝ) =
      threshold p k ^ qBreakpoint p k ∧
    qBreakpoint p k =
      1 + 1 / primePowerSum p k ∧
    (∀ n : ℕ, Real.exp 1 < (n : ℝ) → additionLogDomain n p →
      (0 < Real.log (robinG (n * p)) - Real.log (robinG n) ↔
        threshold p (Nat.factorization n p + 1) < Real.log (n : ℝ)))

def divisorMultiplicity (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, Nat.factorization n p

def twoSidedPrimeNeighborMax (n : ℕ) : Prop :=
  (∀ p : ℕ, Nat.Prime p → robinG n ≥ robinG (n * p)) ∧
  (∀ p : ℕ, Nat.Prime p → p ∣ n → robinG n ≥ robinG (n / p))

def chamberConditions (n : ℕ) : Prop :=
  (∀ p : ℕ, Nat.Prime p →
    breakpointF p (Nat.factorization n p + 1) ≤
      etaP p (Real.log (n : ℝ))) ∧
  (∀ p : ℕ, Nat.Prime p → p ∣ n →
    breakpointF p (Nat.factorization n p) ≥
      etaP p (Real.log (n : ℝ) - Real.log (p : ℝ)))

def claim42929 : Prop :=
  ∀ n : ℕ, Real.exp 1 < (n : ℝ) → 3 ≤ divisorMultiplicity n →
    (twoSidedPrimeNeighborMax n ↔ chamberConditions n)

def claim42930 : Prop :=
  ∀ n : ℕ, Real.exp 1 < (n : ℝ) → 3 ≤ divisorMultiplicity n →
    twoSidedPrimeNeighborMax n →
      (∀ p : ℕ, Nat.Prime p → p ∣ n →
        breakpointF p (Nat.factorization n p + 1) < epsilon n ∧
          epsilon n < breakpointF p (Nat.factorization n p)) ∧
      (∀ p : ℕ, Nat.Prime p → ¬p ∣ n →
        breakpointF p 1 < epsilon n)

def objective (eps : ℝ) (m : ℕ) : ℝ :=
  divisorSum m / (m : ℝ) ^ (1 + eps)

def isUniqueMaximizer (eps : ℝ) (N : ℕ) : Prop :=
  1 ≤ N ∧
    (∀ m : ℕ, 1 ≤ m → objective eps m ≤ objective eps N) ∧
    (∀ m : ℕ, 1 ≤ m → objective eps m = objective eps N → m = N)

def exponentPattern (eps : ℝ) (N : ℕ) : Prop :=
  ∀ (p k : ℕ), Nat.Prime p → 1 ≤ k →
    (k ≤ Nat.factorization N p ↔ breakpointF p k > eps)

def claim42931 : Prop :=
  ∀ eps : ℝ,
    (∀ p k : ℕ, Nat.Prime p → 1 ≤ k → breakpointF p k ≠ eps) →
      (∀ p k : ℕ, Nat.Prime p → 1 ≤ k →
        objective eps (p ^ k) / objective eps (p ^ (k - 1)) =
          Real.exp (Real.log (p : ℝ) * (breakpointF p k - eps))) ∧
      (∃! N : ℕ, isUniqueMaximizer eps N ∧ exponentPattern eps N)

def claim42932 : Prop :=
  ∀ n : ℕ, Real.exp 1 < (n : ℝ) → 3 ≤ divisorMultiplicity n →
    twoSidedPrimeNeighborMax n → isUniqueMaximizer (epsilon n) n

def marginConditions (n : ℕ) : Prop :=
  (∀ p : ℕ, Nat.Prime p → 0 ≤ additionMargin p n) ∧
  (∀ p : ℕ, Nat.Prime p → p ∣ n → 0 ≤ removalMargin p n)

def claim42933 : Prop :=
  (∃ n : ℕ,
    Real.exp 1 < (n : ℝ) ∧ 3 ≤ divisorMultiplicity n ∧
      isUniqueMaximizer (epsilon n) n ∧ ¬twoSidedPrimeNeighborMax n) ∧
  (∀ n : ℕ, Real.exp 1 < (n : ℝ) → 3 ≤ divisorMultiplicity n →
    twoSidedPrimeNeighborMax n ↔
      (isUniqueMaximizer (epsilon n) n ∧ marginConditions n))

def claim42935 : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    (∃! T : ℝ, 1 < T ∧ etaP p T = breakpointF p 1) ∧
    threshold p 1 + Real.log (p : ℝ) =
      threshold p 1 ^ (1 + 1 / (p : ℝ))

def claim42936 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ,
    ∀ p : ℕ, Nat.Prime p → P ≤ p →
      let L : ℝ := Real.log (p : ℝ)
      |threshold p 1 -
          ((p : ℝ) - L ^ 2 / (2 * (L + 1)) +
            L ^ 3 * (2 * L ^ 2 + 7 * L + 8) /
              (24 * (L + 1) ^ 3 * (p : ℝ)) -
            L ^ 4 * (L + 2) * (2 * L ^ 2 + 5 * L + 6) /
              (48 * (L + 1) ^ 5 * (p : ℝ) ^ 2))| ≤
        C * |L| ^ 3 / (p : ℝ) ^ 3

def tailDifference (y p : ℝ) : ℝ :=
  p * Real.log p - (y + Real.log p) * Real.log (y + Real.log p)

def witness : ℕ := 160626866400

def claim42940 : Prop :=
  (∀ p : ℕ, Nat.Prime p →
    breakpointF p 1 < 1 / ((p : ℝ) * Real.log (p : ℝ))) ∧
  (∀ p : ℕ, Nat.Prime p → ∀ y : ℝ, 1 < y →
    etaP p y >
      1 / ((y + Real.log (p : ℝ)) * Real.log (y + Real.log (p : ℝ)))) ∧
  (let y : ℝ := Real.log (witness : ℝ)
   0 < tailDifference y 31 ∧
   StrictMonoOn (tailDifference y) (Set.Ici (31 : ℝ)) ∧
   ∀ p : ℕ, Nat.Prime p → 31 ≤ p → breakpointF p 1 < etaP p y)

def claim42941 : Prop :=
  (∀ p : ℕ, Nat.Prime p → robinG witness ≥ robinG (witness * p)) ∧
  (∀ p : ℕ, Nat.Prime p → p ∣ witness →
    robinG witness ≥ robinG (witness / p))

def claim42944 : Prop :=
  (249853405063844 : ℝ) / 10000000000000 < Real.log (witness : ℝ) ∧
  Real.log (witness : ℝ) <
    (277370963470337 : ℝ) / 10000000000000 ∧
  threshold 23 1 + Real.log (23 : ℝ) < Real.log (witness : ℝ) ∧
  Real.log (witness : ℝ) < threshold 29 1

end
end MathlibPlus.Open.ResearchFormalizationBatch.Robin
