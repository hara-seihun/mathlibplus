import Mathlib

namespace MathlibPlus.Algebra.AdmittedClaimIdentities

/-- Claim 24871: the displayed Pascal matrix has determinant one and is
unimodular, represented by a unit determinant over `ℤ`. -/
theorem pascalLabelMatrixIsUnimodular (k : ℕ) :
    let W : Matrix (Fin k) (Fin k) ℤ :=
      fun j a => (Nat.choose a.val j.val : ℤ)
    W.det = 1 ∧ IsUnit W.det := by
  dsimp
  let W : Matrix (Fin k) (Fin k) ℤ :=
    fun j a => (Nat.choose a.val j.val : ℤ)
  change W.det = 1 ∧ IsUnit W.det
  have hdet : W.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · apply Finset.prod_eq_one
      intro i hi
      simp [W, Nat.choose_self]
    · intro i j hji
      change (Nat.choose j.val i.val : ℤ) = 0
      exact_mod_cast Nat.choose_eq_zero_of_lt hji
  exact ⟨hdet, by rw [hdet]; exact isUnit_one⟩

end MathlibPlus.Algebra.AdmittedClaimIdentities
