import MathlibPlus.Open.ResearchFormalizationBatch.Robin

namespace MathlibPlus.Open.ResearchFormalization.R2627.Claim42937

open MathlibPlus.Open.ResearchFormalizationBatch.Robin

noncomputable section

/-- A largest prime divisor occurring to exponent one. -/
def largestExponentOnePrime (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ valuation q n = 1 ∧
    ∀ r : ℕ, Nat.Prime r → r ∣ n → valuation r n = 1 → r ≤ q

/-- The least prime absent from `n`. -/
def leastAbsentPrime (n p : ℕ) : Prop :=
  Nat.Prime p ∧ ¬ p ∣ n ∧
    ∀ r : ℕ, Nat.Prime r → ¬ r ∣ n → p ≤ r

/-- No higher-power breakpoint lies inside the outer exponent-one chamber.
The removal comparison is made in the `log n` coordinate, so its breakpoint
is `T(r,a)+log r` and the lower outer boundary is `T(q,1)+log q`. -/
def noHigherPrimePowerBreakpointCloser
    (n q p : ℕ) : Prop :=
  ∀ r : ℕ, Nat.Prime r → r ∣ n →
    threshold p 1 ≤ threshold r (valuation r n + 1) ∧
      (valuation r n = 1 ∨
        threshold r (valuation r n) + Real.log (r : ℝ) ≤
          threshold q 1 + Real.log (q : ℝ))

/-- Claim 42937: the conditional outer exponent-one prime-frontier window. -/
def claim42937 : Prop :=
  ∀ (n q p : ℕ),
    Real.exp 1 < (n : ℝ) →
    3 ≤ divisorMultiplicity n →
    twoSidedPrimeNeighborMax n →
    largestExponentOnePrime n q →
    leastAbsentPrime n p →
    noHigherPrimePowerBreakpointCloser n q p →
      threshold q 1 + Real.log (q : ℝ) ≤ Real.log (n : ℝ) ∧
        Real.log (n : ℝ) ≤ threshold p 1

end

end MathlibPlus.Open.ResearchFormalization.R2627.Claim42937
