import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0043Claim687

open scoped BigOperators

noncomputable section

/-- Claim 687: the restricted x²ψ boundary determinant formula, with the
reciprocal-parameter relation made explicit. -/
def claim687 : Prop :=
  ∀ (n : ℕ) (x a : Fin n → ℝ),
    (∀ j, a j * x j = 1) →
    let ψ : Polynomial ℝ :=
      ∏ j : Fin n, (Polynomial.X + Polynomial.C (x j))
    let f : Polynomial ℝ := Polynomial.X ^ 2 * ψ
    let B : ℝ := ∑ j : Fin n, (a j) ^ 2
    let D : ℝ := ∑ j : Fin n, (a j) ^ 4
    Matrix.det (fun i j : Fin 4 =>
      Polynomial.eval 0 ((Polynomial.derivative^[i.val + j.val]) f)) =
      144 * (Polynomial.eval 0 ψ) ^ 4 * (10 * D - B ^ 2)

end
end MathlibPlus.Open.ResearchFormalization.C0043Claim687
