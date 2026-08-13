import Mathlib

namespace MathlibPlus.Analysis.Claim1001

/-- Exact anti-triangular determinant core of the rank-seven derivative-Hankel
calculation.  The two hypotheses are the zero-above-the-reversal and constant
reversal-diagonal conditions supplied by an exact degree-six polynomial. -/
theorem rankSevenAntiTriangularDeterminant
    (M : Matrix (Fin 7) (Fin 7) ℝ) (a : ℝ)
    (hzero : ∀ i j : Fin 7, 6 < (i : ℕ) + (j : ℕ) → M i j = 0)
    (hdiag : ∀ i : Fin 7, M i (Fin.rev i) = 720 * a) :
    M.det = -(720 * a) ^ 7 ∧ -M.det = (720 * a) ^ 7 := by
  let B : Matrix (Fin 7) (Fin 7) ℝ :=
    (Matrix.reindex (Equiv.refl (Fin 7)) Fin.revPerm) M
  have hBupper : B.IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := by simpa only [id_eq] using hij
    rw [show B i j = M i (Fin.rev j) by simp [B, Matrix.reindex_apply]]
    apply hzero
    simp only [Fin.rev]
    omega
  have hBdet : B.det = (720 * a) ^ 7 := by
    rw [Matrix.det_of_isUpperTriangular hBupper]
    have hdiagB : ∀ i : Fin 7, B i i = 720 * a := by
      intro i
      rw [show B i i = M i (Fin.rev i) by simp [B, Matrix.reindex_apply], hdiag]
    simp_rw [hdiagB]
    simp
  have hreindex : B.det = (Fin.revPerm : Equiv.Perm (Fin 7)).sign * M.det := by
    exact Matrix.det_reindex (Equiv.refl (Fin 7)) Fin.revPerm M
  rw [hBdet] at hreindex
  have hsign : (Fin.revPerm : Equiv.Perm (Fin 7)).sign = (-1 : ℤˣ) := by
    decide
  rw [hsign] at hreindex
  norm_num at hreindex ⊢
  constructor
  · linarith
  · linarith

/-- If a polynomial has exact degree six, its seventh derivative-Hankel
matrix has precisely the anti-triangular determinant in the source claim. -/
theorem rankSevenDerivativeDeterminant (p : Polynomial ℝ) (x a : ℝ)
    (hp : p.natDegree = 6) (ha : p.leadingCoeff = a) :
    (let M : Matrix (Fin 7) (Fin 7) ℝ := fun i j =>
      ((Polynomial.derivative^[((i : ℕ) + (j : ℕ))]) p).eval x
     M.det = -(720 * a) ^ 7) := by
  let M : Matrix (Fin 7) (Fin 7) ℝ := fun i j =>
    ((Polynomial.derivative^[((i : ℕ) + (j : ℕ))]) p).eval x
  dsimp only
  have hcore : M.det = -(720 * a) ^ 7 ∧ -M.det = (720 * a) ^ 7 := by
    apply rankSevenAntiTriangularDeterminant M a
    · intro i j hij
      dsimp [M]
      have hdeg : p.natDegree < (i : ℕ) + (j : ℕ) := by
        rw [hp]
        exact hij
      rw [Polynomial.iterate_derivative_eq_zero hdeg]
      simp
    · intro i
      change ((Polynomial.derivative^[((i : ℕ) + (Fin.rev i : ℕ))]) p).eval x = 720 * a
      have hsum : (i : ℕ) + (Fin.rev i : ℕ) = 6 := by
        exact Fin.add_rev_cast i
      have hder : (Polynomial.derivative^[6]) p = Polynomial.C (720 * a) := by
        have hn : (Polynomial.derivative^[6] p).natDegree ≤ 0 := by
          simpa [hp] using Polynomial.natDegree_iterate_derivative p 6
        have hn0 : (Polynomial.derivative^[6] p).natDegree = 0 :=
          Nat.eq_zero_of_le_zero hn
        rw [Polynomial.eq_C_of_natDegree_eq_zero hn0]
        congr 1
        rw [Polynomial.coeff_iterate_derivative]
        have hcoeff : p.coeff 6 = a := by
          have hcoeff' : p.coeff p.natDegree = a := by simpa using ha
          simpa [hp] using hcoeff'
        norm_num [hp, hcoeff]
      rw [show ((Polynomial.derivative^[((i : ℕ) + (Fin.rev i : ℕ))]) p).eval x =
          ((Polynomial.derivative^[6]) p).eval x by rw [hsum], hder]
      simp
  exact hcore.1

end MathlibPlus.Analysis.Claim1001
