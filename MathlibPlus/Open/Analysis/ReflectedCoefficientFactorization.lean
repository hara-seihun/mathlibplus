import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The rising factorial used in the exact reflected-row expansion. -/
def risingFactor (a : ℝ) (m : ℕ) : ℝ :=
  Finset.prod (Finset.range m) (fun j => a + (j : ℝ))

/-- The reflected polynomial supplied by the Laguerre-row expansion in the repair context. -/
noncomputable def reflectedRow (i : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (i + 2)) (fun k =>
    Polynomial.C
        ((Nat.choose (i + 1) k : ℝ) *
          risingFactor (((i + k : ℕ) : ℝ) + 3 / 2) (i + 1 - k)) *
      Polynomial.X ^ (i + k))

/-- Reflected coefficient factorization, entrywise on the displayed reflected row. -/
def reflected_coefficient_factorization : Prop :=
  ∀ (i n : ℕ),
    i ≤ n →
    n ≤ 2 * i + 1 →
    (reflectedRow i).coeff n =
      Real.Gamma ((2 * (i : ℝ)) + 5 / 2) /
          Real.Gamma ((n : ℝ) + 3 / 2) *
        (Nat.choose (i + 1) (n - i) : ℝ)

end MathlibPlus.Open.Analysis
