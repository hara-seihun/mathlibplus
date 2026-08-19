import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3423FortyFiveObstruction

noncomputable section

/-- Claim 50216: the exact n=45 binomial-gcd height and its minimal divisor
obstruction give the displayed valuation and strict f(45) bound. -/
def fortyFiveMinimalDivisorObstruction_claim50216 : Prop :=
  let H : ℕ → ℕ → ℕ := fun n k =>
    n / Nat.gcd n (Nat.choose n k)
  let Q : ℕ → ℕ := fun n =>
    (Nat.factorization n).support.sup
      (fun p => p ^ Nat.factorization n p)
  let M : ℕ → ℕ → ℕ → Prop := fun n q d =>
    d ∣ n ∧ q < d ∧
      (∀ e : ℕ, e ∣ d → e < d → e ≤ q)
  let f : ℕ → ℚ := fun n =>
    (n : ℚ) /
      ((Finset.Icc 2 (n / 2)).sup (H n))
  Q 45 = 9 ∧
    H 45 15 = 15 ∧
    M 45 (Q 45) 15 ∧
    15 ∣ H 45 15 ∧
    H 45 15 > Q 45 ∧
    padicValNat 3 (Nat.choose 45 15) = 1 ∧
    padicValNat 5 (Nat.choose 45 15) = 0 ∧
    21 - 6 - 14 = 1 ∧
    10 - 3 - 7 = 0 ∧
    f 45 < (45 : ℚ) / 9

end

end MathlibPlus.Open.ResearchFormalization.R3423FortyFiveObstruction
