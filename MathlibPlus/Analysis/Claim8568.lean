import Mathlib

namespace MathlibPlus.Analysis.Claim8568

/-- The dual hole-weight formula is strictly positive once the implicit
positive-weight and simple-node (nonzero derivative) context is made explicit.
The polynomial is retained exactly as the product of the node factors. -/
theorem dual_complement_weight_pos_claim8568
    {n : ℕ} (x w : Fin n → ℝ) (A : Polynomial ℝ)
    (hA : A = ∏ i : Fin n, (Polynomial.X - Polynomial.C (x i)))
    (hw : ∀ i, 0 < w i)
    (hderiv : ∀ i, (Polynomial.derivative A).eval (x i) ≠ 0) :
    ∀ i, 0 < 1 / (w i * ((Polynomial.derivative A).eval (x i)) ^ 2) := by
  rw [hA] at hderiv ⊢
  intro i
  have hwi : 0 < w i := hw i
  have hdi : 0 <
      ((Polynomial.derivative
        (∏ j : Fin n, (Polynomial.X - Polynomial.C (x j)))).eval (x i)) ^ 2 :=
    sq_pos_of_ne_zero (hderiv i)
  positivity

end MathlibPlus.Analysis.Claim8568
