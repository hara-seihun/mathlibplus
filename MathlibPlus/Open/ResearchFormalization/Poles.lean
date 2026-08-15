import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Poles

open scoped BigOperators

/-- The two-pole finite dominant-pole matrix. -/
def poleMatrix (r : Nat) (x c : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∑ p : Fin 2, c p * x p ^ (r + j.val - i.val)

/-- Positivity of the ordered two-pole determinant. -/
def claim4430 : Prop :=
  ∀ (r : Nat) (x c : Fin 2 → ℝ),
    1 ≤ r →
    0 < x 1 ∧ x 1 < x 0 ∧ c 0 > 0 ∧ c 1 < 0 →
    (poleMatrix r x c).det > 0

end MathlibPlus.Open.ResearchFormalization.Poles
