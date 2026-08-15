import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CountingClaims

private def firstCountSet (A : ℕ) : Finset (ℤ × ℤ) :=
  let bound : ℤ := 12 * (A : ℤ)
  (Finset.Icc (1 : ℤ) bound ×ˢ Finset.Icc (1 : ℤ) bound).filter
    (fun p =>
      12 ∣ p.1 + p.2 ∧
      5 * p.1 ≥ p.2 - 36 ∧
      p.1 ≤ 3 * p.2 ∧
      p.1 + p.2 ≤ bound)

private def secondCountSet (A : ℕ) : Finset (ℤ × ℤ) :=
  let bound : ℤ := 12 * (A : ℤ)
  (Finset.Icc (1 : ℤ) bound ×ˢ Finset.Icc (1 : ℤ) bound).filter
    (fun p =>
      12 ∣ p.1 + p.2 ∧
      5 * p.1 ≥ p.2 - 36 ∧
      p.1 ≤ 3 * p.2 ∧
      p.1 + p.2 ≤ bound)

/-- The cumulative count with the first coordinate named K². -/
def r59754_numerically_admissible_cumulative_count_k_squared : Prop :=
  ∀ A : ℕ, 0 < A →
    (firstCountSet A).card =
      if A ≤ 3 then 9 * A * (A + 1) / 2
      else (7 * A ^ 2 + 21 * A - 18) / 2

/-- The cumulative count with an ordinary integer first coordinate. -/
def r59755_numerically_admissible_cumulative_count : Prop :=
  ∀ A : ℕ, 0 < A →
    (secondCountSet A).card =
      if A ≤ 2 then 9 * A * (A + 1) / 2
      else (7 * A ^ 2 + 21 * A - 18) / 2

end MathlibPlus.Open.ResearchFormalization.CountingClaims
