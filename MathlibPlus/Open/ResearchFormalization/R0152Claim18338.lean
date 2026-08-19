import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0152Claim18338

noncomputable section

/-- Claim 18338: the explicit real two-by-two pencil has distinct simple real
 determinant roots but no positive-semidefinite member. -/
def realSimpleRootsDoNotImplyFeasibility_claim18338 : Prop :=
  let C : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 0; 0, 1]
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  let pencil : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun lambda => C + lambda • A
  let determinant : ℝ → ℝ := fun lambda => Matrix.det (pencil lambda)
  (∀ lambda : ℝ,
      pencil lambda = !![lambda - 2, 0; 0, 1 - lambda]) ∧
    (∀ lambda : ℝ,
      determinant lambda = (lambda - 2) * (1 - lambda)) ∧
    (∀ lambda : ℝ,
      determinant lambda = 0 ↔ lambda = 1 ∨ lambda = 2) ∧
    deriv determinant 1 ≠ 0 ∧
    deriv determinant 2 ≠ 0 ∧
    (∀ lambda : ℝ, ¬ Matrix.PosSemidef (pencil lambda)) ∧
    (∀ lambda : ℝ,
      Matrix.PosSemidef (pencil lambda) → lambda ≥ 2 ∧ lambda ≤ 1)

end

end MathlibPlus.Open.ResearchFormalization.R0152Claim18338
