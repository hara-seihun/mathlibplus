import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.OrientedCofactors

noncomputable def thetaKernel (u : ℝ) : ℝ :=
  Real.exp (u / 2) * ∑' n : ℕ,
    Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u))

noncomputable def derivativeMoment (m N : ℕ) : ℝ :=
  (2 : ℝ) / (↑(Nat.factorial (2 * N)) : ℝ) *
    ∫ u in Set.Ioi (0 : ℝ),
      iteratedDeriv (2 * m) thetaKernel u * u ^ (2 * N)

noncomputable def primitiveMatrix (r k : ℕ) : Matrix (Fin (r + 1)) (Fin r) ℝ :=
  fun m j => derivativeMoment m.val (k + j.val)

def deletedRowMinor {r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin r) ℝ) (m : Fin (r + 1)) :
    Matrix (Fin r) (Fin r) ℝ :=
  A.submatrix (Fin.succAbove m) (fun j => j)

noncomputable def maximalMinor {r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin r) ℝ) (m : Fin (r + 1)) : ℝ :=
  Matrix.det (deletedRowMinor A m)

noncomputable def orientedCofactorVector {r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin r) ℝ) : Fin (r + 1) → ℝ :=
  fun m => (-1 : ℝ) ^ m.val * maximalMinor A m

def leftNullspace {r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin r) ℝ) :
    Submodule ℝ (Fin (r + 1) → ℝ) :=
  LinearMap.ker (Matrix.toLin' A.transpose)

def orientedCofactorsFormLeftNullVector (r k : ℕ) : Prop :=
  let A := primitiveMatrix r k
  let q := orientedCofactorVector A
  q ∈ leftNullspace A ∧
    (Matrix.rank A = r →
      Module.finrank ℝ (leftNullspace A) = 1 ∧
        leftNullspace A = Submodule.span ℝ ({q} : Set (Fin (r + 1) → ℝ)))

end MathlibPlus.Open.LinearAlgebra.OrientedCofactors
