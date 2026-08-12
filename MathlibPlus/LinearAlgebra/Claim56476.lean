import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Rat.Cast.Order

namespace MathlibPlus.LinearAlgebra.Claim56476

open scoped BigOperators

/-- A positive circuit annihilates every linear part of an affine response, so
only the constant offset survives in the weighted response sum. -/
theorem positiveCircuitAffineResponse
    {S W : Type*} [Fintype S] [AddCommGroup W] [Module ℚ W]
    (q : S → ℚ) (ell : S → W) (a : S → ℚ)
    (barA : ℚ) (Phi : W →ₗ[ℚ] ℚ)
    (hq : ∀ e, 0 < q e)
    (hbar : barA ≠ 0)
    (hcycle : ∑ e, q e • ell e = 0)
    (hdecomp : ∀ e, a e = barA + Phi (ell e)) :
    ∑ e, q e * a e = (∑ e, q e) * barA := by
  have hPhi : ∑ e, q e * Phi (ell e) = 0 := by
    calc
      ∑ e, q e * Phi (ell e) = ∑ e, Phi (q e • ell e) := by
        apply Finset.sum_congr rfl
        intro e he
        simp only [map_smul, smul_eq_mul]
      _ = Phi (∑ e, q e • ell e) := by rw [map_sum]
      _ = 0 := by rw [hcycle, map_zero]
  calc
    ∑ e, q e * a e = ∑ e, q e * (barA + Phi (ell e)) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hdecomp e]
    _ = (∑ e, q e) * barA + ∑ e, q e * Phi (ell e) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ e, q e) * barA := by rw [hPhi, add_zero]

end MathlibPlus.LinearAlgebra.Claim56476
