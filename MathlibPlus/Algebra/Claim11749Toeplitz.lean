import Mathlib

namespace MathlibPlus.Algebra.AdmittedClaimIdentities

/-- Claim 11749: with `T i j = c (j - i)`, the first displayed boundary
minor (rows 0,1,2 and columns 1,2,3) has the stated determinant. -/
theorem boundaryToeplitzMinorDet {R : Type*} [CommRing R] (c : ℤ → R)
    (hneg : ∀ n : ℤ, n < 0 → c n = 0) :
    let T : ℤ → ℤ → R := fun i j => c (j - i)
    let M : Matrix (Fin 3) (Fin 3) R :=
      fun i j => T (i.val : ℤ) ((j.val : ℤ) + 1)
    M.det = c 1 ^ 3 - 2 * c 0 * c 1 * c 2 + c 0 ^ 2 * c 3 := by
  dsimp
  rw [Matrix.det_fin_three
    (fun i j => c ((j.val : ℤ) + 1 - (i.val : ℤ)))]
  simp [hneg]
  ring

end MathlibPlus.Algebra.AdmittedClaimIdentities
