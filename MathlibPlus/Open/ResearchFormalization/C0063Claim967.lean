import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0063Claim967

/-- The order-seven derivative determinant for the product with six positive
reciprocal-root parameters has the exact displayed product scale.  The
polynomial and determinant carriers remain local to this claim. -/
def exactSixPositiveRootDeterminant_claim967 : Prop :=
  ∀ α : Fin 6 → ℝ,
    (∀ i, 0 < α i) →
      let G : Polynomial ℝ :=
        ∏ i : Fin 6, (1 + Polynomial.C (α i) * Polynomial.X)
      let D₇ : ℝ :=
        Matrix.det (fun i j : Fin 7 =>
          (((Polynomial.derivative^[6 + j - i]) G).eval 0))
      D₇ = (720 : ℝ) ^ 7 * (∏ i : Fin 6, α i) ^ 7 ∧
        (720 : ℝ) ^ 7 * (∏ i : Fin 6, α i) ^ 7 =
          (100306130042880000000 : ℝ) * (∏ i : Fin 6, α i) ^ 7 ∧
        0 < (720 : ℝ) ^ 7 * (∏ i : Fin 6, α i) ^ 7

end MathlibPlus.Open.ResearchFormalization.C0063Claim967
