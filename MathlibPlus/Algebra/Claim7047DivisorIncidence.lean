import Mathlib

namespace MathlibPlus.Algebra

/-- The finite divisor-incidence matrix is identity plus a nilpotent strict
upper-triangular part when its finite index order is compatible with
 divisibility, as in admitted claim 7047. -/
theorem finite_divisor_incidence_zeta_operator_claim7047
    (n : ℕ) (d : Fin n → ℕ)
    (hcompat : ∀ i j, d i ∣ d j → i ≤ j) :
    let Z : Matrix (Fin n) (Fin n) ℤ := fun i j =>
      if d i ∣ d j then 1 else 0
    let N : Matrix (Fin n) (Fin n) ℤ := Z - 1
    Z = 1 + N ∧ N ^ n = 0 := by
  dsimp
  let Z : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    if d i ∣ d j then 1 else 0
  let N : Matrix (Fin n) (Fin n) ℤ := Z - 1
  have hupperZ : Z.IsUpperTriangular := by
    intro i j hij
    have hnot : ¬ d i ∣ d j := by
      intro hdiv
      have hle : i ≤ j := hcompat i j hdiv
      exact (not_le_of_gt hij) hle
    simp [Z, hnot]
  have hupperN : N.IsUpperTriangular := by
    intro i j hij
    have hne : i ≠ j := by
      intro heq
      subst i
      exact (lt_irrefl _ hij)
    simp [N, hupperZ hij, hne]
  have hdiagN : ∀ i, N i i = 0 := by
    intro i
    change Z i i - (1 : Matrix (Fin n) (Fin n) ℤ) i i = 0
    simp [Z]
  have hchar : N.charpoly = Polynomial.X ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular N hupperN]
    simp [hdiagN]
  have hCH := Matrix.aeval_self_charpoly N
  rw [hchar] at hCH
  constructor
  · ext i j
    change Z i j =
      (1 : Matrix (Fin n) (Fin n) ℤ) i j +
        (Z i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j)
    ring
  · simpa [Polynomial.aeval_def] using hCH

end MathlibPlus.Algebra
