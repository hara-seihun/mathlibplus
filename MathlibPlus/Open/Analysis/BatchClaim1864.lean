import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact Q-ratios and the two positive cleared differences. -/
def claim1864 : Prop :=
  ∀ (d n ell : ℕ),
    (2 ≤ n ∧ 1 ≤ ell ∧ max n (ell + 2) ≤ d) →
      let Q : ℕ → ℕ → ℚ := fun n' ell' =>
        (((d + 1 : ℕ) : ℚ) * ((d + n' : ℕ) : ℚ) /
            ((d : ℚ) * ((ell' + 2 : ℕ) : ℚ))) *
          (Nat.choose d n' : ℚ) *
          (Nat.choose (d + ell' + 2) (ell' + 1) : ℚ)
      (Q n ell / Q n (ell - 1) =
          ((d + ell + 2 : ℕ) : ℚ) / ((ell + 2 : ℕ) : ℚ) ∧
        Q n ell / Q (n - 1) ell =
          (((d + n : ℕ) : ℚ) * ((d - n + 1 : ℕ) : ℚ)) /
            (((n : ℚ) * ((d + n - 1 : ℕ) : ℚ))) ∧
        (2 ≤ ell →
          (((d : ℚ) - (ell : ℚ)) * Q n (ell - 1) - Q n ell =
              (((ell + 1 : ℕ) : ℚ) *
                  ((d : ℚ) - (ell : ℚ) - 2)) /
                ((ell + 2 : ℕ) : ℚ) * Q n (ell - 1)) ∧
            0 ≤ ((d : ℚ) - (ell : ℚ)) * Q n (ell - 1) - Q n ell) ∧
        (3 ≤ n →
          (((d + n : ℕ) : ℚ) * Q (n - 1) ell - Q n ell =
              ((((d + n : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) *
                    ((d + n + 1 : ℕ) : ℚ)) /
                (((n : ℚ) * ((d + n - 1 : ℕ) : ℚ))) * Q (n - 1) ell)) ∧
            0 < ((d + n : ℕ) : ℚ) * Q (n - 1) ell - Q n ell))

end MathlibPlus.Open.Analysis
