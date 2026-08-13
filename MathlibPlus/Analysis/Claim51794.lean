import Mathlib

namespace MathlibPlus.Analysis.Claim51794

private noncomputable def a : ℝ := 5 / 4

private def sign (b : Bool) : ℝ := if b then 1 else -1

private noncomputable def H (q u : ℝ) : ℝ :=
  Real.exp (-2 * a * u - q * Real.exp (-2 * u)) +
    Real.exp (2 * a * u - q * Real.exp (2 * u))

/-- The chamber expansion in claim 51794.  The strict ordering of the knots is
retained as a hypothesis, although multilinearity makes the identity algebraic. -/
theorem determinant_chamber_expansion_claim51794
    (r : ℕ) (q u : Fin r → ℝ) (_hu : StrictMono u) :
    Matrix.det (fun i j => H (q i) (u j)) =
      ∑ ε : Fin r → Bool,
        Real.exp (2 * a * ∑ j, sign (ε j) * u j) *
          Matrix.det (fun i j =>
            Real.exp (-q i * Real.exp (2 * sign (ε j) * u j))) := by
  have hentry (i j : Fin r) :
      H (q i) (u j) =
        ∑ b : Bool,
          Real.exp (2 * a * sign b * u j) *
            Real.exp (-q i * Real.exp (2 * sign b * u j)) := by
    simp [H, a, sign]
    rw [add_comm]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
  classical
  have hweight (ε : Fin r → Bool) :
      Real.exp (∑ j, 2 * a * (sign (ε j) * u j)) =
        ∏ j, Real.exp (2 * a * sign (ε j) * u j) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    ring
  rw [Matrix.det_apply' (fun i j => H (q i) (u j))]
  simp_rw [hentry]
  let K : (Fin r → Bool) → Matrix (Fin r) (Fin r) ℝ := fun ε i j =>
    Real.exp (-q i * Real.exp (2 * sign (ε j) * u j))
  have hK (ε : Fin r → Bool) := Matrix.det_apply' (K ε)
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  change _ = ∑ ε, Real.exp (∑ j, 2 * a * (sign (ε j) * u j)) * (K ε).det
  simp_rw [hK]
  simp_rw [Finset.prod_mul_distrib]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε hε
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [hweight]
  simp [K]
  ring

end MathlibPlus.Analysis.Claim51794
