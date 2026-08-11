import Mathlib

namespace MathlibPlus.Analysis.Claim11118

noncomputable section

abbrev Vec := Fin 2 → ℝ

/-- The diagonal operator `diag(2,-2)` in the displayed fixture. -/
def J : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![(2 : ℝ), -2]

/-- The action of `J` on a two-coordinate vector. -/
def jAction (w : Vec) : Vec :=
  ![2 * w 0, -2 * w 1]

/-- The direct coordinate formula agrees with multiplication by `J`. -/
theorem jAction_eq_mulVec (w : Vec) : jAction w = J.mulVec w := by
  ext i
  fin_cases i <;> simp [jAction, J, Matrix.mulVec, Fin.sum_univ_two]

/-- The Euclidean dot product on the displayed two-coordinate vectors. -/
def inner (u v : Vec) : ℝ :=
  ∑ i, u i * v i

/-- Orthogonal projection of `w` onto the line spanned by a nonzero `v`. -/
def projection (v w : Vec) : Vec :=
  (inner w v / inner v v) • v

/-- The residual of the `J`-action after projection onto the input line. -/
def residual (v : Vec) : Vec :=
  jAction v - projection v (jAction v)

/-- Squared Euclidean norm, written explicitly for the two-coordinate model. -/
def normSq (w : Vec) : ℝ :=
  ∑ i, w i ^ 2

def mixed : Vec := ![(1 : ℝ), 1]
def e₁ : Vec := ![(1 : ℝ), 0]
def e₂ : Vec := ![(0 : ℝ), 1]
def expectedMixedResidual : Vec := ![(2 : ℝ), -2]

theorem mixed_eigencomponent_fixture :
    projection mixed (jAction mixed) = 0 ∧
      residual mixed = expectedMixedResidual ∧
      normSq (residual mixed) = 8 ∧
      residual e₁ = 0 ∧
      residual e₂ = 0 := by
  dsimp [projection, residual, jAction, J, inner, normSq,
    mixed, e₁, e₂, expectedMixedResidual]
  constructor
  · ext i
    fin_cases i <;> norm_num [jAction, Fin.sum_univ_two]
  constructor
  · ext i
    fin_cases i <;> norm_num [jAction, Fin.sum_univ_two]
  constructor
  · norm_num [jAction, Fin.sum_univ_two]
  constructor
  · ext i
    fin_cases i <;> norm_num [jAction, Fin.sum_univ_two]
  · ext i
    fin_cases i <;> norm_num [jAction, Fin.sum_univ_two]

end

end MathlibPlus.Analysis.Claim11118
