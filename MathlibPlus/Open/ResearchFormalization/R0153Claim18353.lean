import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0153Claim18353

/-- Claim 18353: the exact rank-two Hankel pencil has negative determinant at
 every real parameter and consequently has no positive-semidefinite member. -/
def rankTwoHankelPencil_negativeDet_claim18353 : Prop :=
  let HP : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]
  let HR : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  ∀ lambda : ℝ,
    let pencil : Matrix (Fin 2) (Fin 2) ℝ := HP - lambda • HR
    pencil = !![-1, -lambda; -lambda, 1] ∧
      Matrix.det pencil = -1 - lambda ^ 2 ∧
      Matrix.det pencil < 0 ∧
      ¬ Matrix.PosSemidef pencil

end MathlibPlus.Open.ResearchFormalization.R0153Claim18353
