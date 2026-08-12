import Mathlib

/-!
# Scalar Adams action and distinct-root obstruction (claim 12300)

The source's weight summand and Adams operator are represented by their exact
two-dimensional scalar matrix model.  The second declaration records the
stated incompatibility with a monic quadratic having two distinct roots.
-/

namespace MathlibPlus.LinearAlgebra.Claim12300

/-- The characteristic polynomial of the scalar action `q^j` on a two-dimensional
summand is `(T-q^j)^2`. -/
theorem scalar_adams_charpoly_claim12300
    {K : Type*} [Field K] (q : K) (j : ℕ) :
    Matrix.charpoly ((q ^ j : K) • (1 : Matrix (Fin 2) (Fin 2) K)) =
      (Polynomial.X - Polynomial.C (q ^ j)) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace]
  have hc2 : (Polynomial.C (2 : K) : Polynomial K) = 2 :=
    Polynomial.C_ofNat 2
  rw [hc2]
  ring

/-- A scalar quadratic cannot equal a quadratic with two distinct roots. -/
theorem scalar_action_cannot_match_distinct_roots_claim12300
    {K : Type*} [Field K] (u v a : K) (huv : u ≠ v) :
    (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) ≠
      (Polynomial.X - Polynomial.C a) ^ 2 := by
  intro h
  have hu := congrArg (Polynomial.eval u) h
  have hv := congrArg (Polynomial.eval v) h
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] at hu hv
  have hua : u = a := by
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu.symm)
  have hva : v = a := by
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hv.symm)
  exact huv (hua.trans hva.symm)

/-- The full algebraic interface: `A` is the represented Adams action and `P`
is a monic quadratic with two distinct roots in the same coefficient field. -/
theorem adams_frobenius_obstruction_claim12300
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (q : K) (j : ℕ)
    (P : Polynomial K) (u v : K)
    (hA : A = (q ^ j : K) • (1 : Matrix (Fin 2) (Fin 2) K))
    (hP : P = (Polynomial.X - Polynomial.C u) *
      (Polynomial.X - Polynomial.C v)) (huv : u ≠ v) :
    A.charpoly = (Polynomial.X - Polynomial.C (q ^ j)) ^ 2 ∧
      A.charpoly ≠ P := by
  constructor
  · rw [hA]
    exact scalar_adams_charpoly_claim12300 q j
  · rw [hA, scalar_adams_charpoly_claim12300 q j, hP]
    intro h
    exact scalar_action_cannot_match_distinct_roots_claim12300 u v (q ^ j) huv h.symm

end MathlibPlus.LinearAlgebra.Claim12300
