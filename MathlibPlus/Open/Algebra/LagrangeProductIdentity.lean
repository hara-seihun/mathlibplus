import Mathlib

namespace MathlibPlus.Open.Algebra

/-- The exact Lagrange-product identity from claim 47245. The polynomial is
formed from the supplied distinct nodes, and the product over `i < j` is
written as a nested finite product on `Fin n`. -/
def lagrangeProductIdentity_claim47245 : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ),
    1 ≤ n →
    (∀ i j, i ≠ j → t i ≠ t j) →
    (∀ i, t i ∈ Set.Icc (-1 : ℝ) 1) →
    ∀ x : ℝ, (∀ i, x ≠ t i) →
      let P : Polynomial ℝ := ∏ i, (Polynomial.X - Polynomial.C (t i))
      let ell : Fin n → ℝ := fun i =>
        P.eval x / ((Polynomial.derivative P).eval (t i) * (x - t i))
      let V : ℝ := ∏ i : Fin n, (∏ j ∈ Finset.Ioi i, |t j - t i|)
      (∏ i, |ell i|) = |P.eval x| ^ (n - 1) / V ^ 2

end MathlibPlus.Open.Algebra
