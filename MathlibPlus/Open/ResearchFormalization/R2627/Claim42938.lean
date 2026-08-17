import MathlibPlus.Open.ResearchFormalizationBatch.Robin

namespace MathlibPlus.Open.ResearchFormalization.R2627.Claim42938

open MathlibPlus.Open.ResearchFormalizationBatch.Robin

noncomputable section

/-- Big-O along the prime integers, with the eventual constant and prime
threshold explicit. -/
def isBigOAlongPrimes (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, Nat.Prime p → p₀ ≤ p →
      |f p| ≤ C * |g p|

def outerLeftMain (p : ℕ) : ℝ :=
  (p : ℝ) + (Real.log (p : ℝ) + 1) / 2 -
    1 / (2 * (Real.log (p : ℝ) + 1))

def outerRightMain (p : ℕ) : ℝ :=
  (p : ℝ) - Real.log (p : ℝ) / 2 + 1 / 2 -
    1 / (2 * (Real.log (p : ℝ) + 1))

def outerLeftThreshold (p : ℕ) : ℝ :=
  threshold p 1 + Real.log (p : ℝ)

def outerRightThreshold (p : ℕ) : ℝ :=
  threshold p 1

def consecutivePrimePair (q p : ℕ) : Prop :=
  Nat.Prime q ∧ Nat.Prime p ∧ q < p ∧
    ∀ r : ℕ, Nat.Prime r → q < r → r < p → False

def outerExponentOneWindowNonempty (q p : ℕ) : Prop :=
  outerLeftThreshold q ≤ outerRightThreshold p

/-- The leading-gap conclusion is stated as an eventual lower bound with
leading coefficient one for every fixed relative error. -/
def leadingLogarithmicPrimeGap : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p₀ : ℕ, ∀ (q p : ℕ),
      consecutivePrimePair q p →
      outerExponentOneWindowNonempty q p →
      p₀ ≤ p →
      (1 - δ) * Real.log (p : ℝ) ≤ (p : ℝ) - (q : ℝ)

/-- Claim 42938: the two prime-directed outer-threshold expansions and the
resulting consecutive-prime leading-gap requirement. -/
def claim42938 : Prop :=
  isBigOAlongPrimes
      (fun p : ℕ => outerLeftThreshold p - outerLeftMain p)
      (fun p : ℕ => (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ∧
    isBigOAlongPrimes
      (fun p : ℕ => outerRightThreshold p - outerRightMain p)
      (fun p : ℕ => (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ∧
    leadingLogarithmicPrimeGap

end

end MathlibPlus.Open.ResearchFormalization.R2627.Claim42938
