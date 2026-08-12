import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.SpectatorBoundary

/-!
Formalization of admitted claim 44417.  The displayed boundary matrices,
top and lower circuit vectors, and the three lower values are encoded exactly
as integer matrices/vectors.  The final source-specific phrase about block
triangularity is not a typed predicate in the packet; the exact arithmetic
core, including the nontrivial lower affine relation, is what is recorded.
-/

/-- The explicit boundary calculation and lower-value relation from claim 44417. -/
theorem spectator_boundary_calculation_claim44417 :
    let dn : Matrix (Fin 3) (Fin 2) ℤ := !![1, 0; -1, 1; 0, -1]
    let sigma : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 1, 1, 0; 0, 1, 2]
    let dm : Matrix (Fin 3) (Fin 2) ℤ := !![1, 0; 0, 1; -1, -1]
    let c : Matrix (Fin 2) (Fin 1) ℤ := !![1; 1]
    let xiA : ℤ × ℤ := (1, 1)
    let xiB : ℤ × ℤ := (1, -1)
    let xiC : ℤ × ℤ := (1, 0)
    sigma * dn = dm ∧
      dn * c = !![1; 0; -1] ∧
      dm * c = !![1; 1; -2] ∧
      xiA ≠ xiB ∧ xiA ≠ xiC ∧ xiB ≠ xiC ∧
      (xiA.1 + xiB.1 - 2 * xiC.1 = 0 ∧
       xiA.2 + xiB.2 - 2 * xiC.2 = 0) := by
  dsimp
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

end MathlibPlus.LinearAlgebra.SpectatorBoundary
