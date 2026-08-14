import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 22426: aligned dyadic block upper bounds chain to every prefix,
with the stated logarithmic scale count for the supplied length. -/
def claim22426 : Prop :=
  ∀ (M J : ℕ) (a : ℕ → ℝ) (B : ℕ → ℝ),
    (M + 1 ≤ 2 ^ J ∧ (J = 0 ∨ 2 ^ (J - 1) < M + 1)) →
      (∀ (j k : ℕ),
          j < J → (k + 1) * 2 ^ j ≤ M →
          (Finset.sum (Finset.range (2 ^ j))
            (fun i => a (k * 2 ^ j + i))) ≤ B j) →
        (∀ r : ℕ, r ≤ M →
          (Finset.sum (Finset.range r) a) ≤
            (Finset.sum (Finset.range J) (fun j => max (B j) 0))) ∧
        (M = 139309012 → J = 28)

end MathlibPlus.Open.Analysis
