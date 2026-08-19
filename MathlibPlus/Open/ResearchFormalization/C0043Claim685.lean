import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0043Claim685

open scoped BigOperators

noncomputable section

/-- The centered fourth-order derivative determinant at the boundary. -/
noncomputable def centeredWronskian4AtZero (f : Polynomial ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 4 =>
    Polynomial.eval 0 ((Polynomial.derivative^[i.val + j.val]) f))

/-- Claim 685: a degree-thirteen real polynomial with pairwise distinct,
strictly negative zeros can have negative centered fourth determinant at zero. -/
def claim685 : Prop :=
  ∃ (f : Polynomial ℝ) (roots : Fin 13 → ℝ) (leading : ℝ),
    leading ≠ 0 ∧
    Function.Injective roots ∧
    (∀ ν, roots ν < 0) ∧
    f = Polynomial.C leading *
      ∏ ν : Fin 13, (Polynomial.X - Polynomial.C (roots ν)) ∧
    f.natDegree = 13 ∧
    centeredWronskian4AtZero f < 0

end
end MathlibPlus.Open.ResearchFormalization.C0043Claim685
