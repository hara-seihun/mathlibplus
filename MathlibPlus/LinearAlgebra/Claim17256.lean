import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim17256

/-- The Hankel minor of the heat-evolved coefficient family `q` at time `t`.
The row and column indices start at `0`, as in the source formula. -/
noncomputable def heatHankelMinor
    (q : ℝ → ℕ → ℝ) (t : ℝ) (r s : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r => q t (s + (i : ℕ) + (j : ℕ)))

/-- The collision order attached to a Hankel rank. -/
def collisionOrder (r : ℕ) : ℕ := Nat.choose r 2

end MathlibPlus.LinearAlgebra.Claim17256
