import Mathlib

namespace MathlibPlus.Algebra.Claim46139

/--
The exact finite-offset normalization for the dyadic weights
`w_a = a / 2^a`.
-/
def offsetNormalForm : Prop :=
  ∀ (n : ℕ) (D : Finset ℕ),
    3 ≤ n →
    2 ≤ D.card →
    (∀ d ∈ D, 0 < d) →
    ((n : ℝ) / (2 : ℝ) ^ n =
        ∑ d ∈ D, ((n + d : ℕ) : ℝ) / (2 : ℝ) ^ (n + d)) ↔
      (n : ℝ) =
        ∑ d ∈ D, ((n + d : ℕ) : ℝ) / (2 : ℝ) ^ d

/--
A finite positive-index representation with at least two distinct summands
cannot use an index at most `n`.
-/
def noIndexLE_of_representation : Prop :=
  ∀ (n : ℕ) (I : Finset ℕ),
    3 ≤ n →
    2 ≤ I.card →
    (∀ a ∈ I, 0 < a) →
    ((n : ℝ) / (2 : ℝ) ^ n =
      ∑ a ∈ I, (a : ℝ) / (2 : ℝ) ^ a) →
    ∀ a ∈ I, n < a

end MathlibPlus.Algebra.Claim46139
