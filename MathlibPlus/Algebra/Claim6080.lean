import Mathlib

namespace MathlibPlus.Algebra.Claim6080

/-- The rooted atom associated with a rooted factor `A_R`. -/
def rootedBoundaryAtom (A_R : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  v + u * A_R u v

theorem rootedBoundaryAtom_eq (A_R : ℝ → ℝ → ℝ) (u v : ℝ) :
    rootedBoundaryAtom A_R u v = v + u * A_R u v := by
  rfl

end MathlibPlus.Algebra.Claim6080
