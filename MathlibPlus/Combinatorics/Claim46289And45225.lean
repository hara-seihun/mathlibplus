import Mathlib

namespace MathlibPlus.Combinatorics.Claim46289

open Matrix

/-- The two off-diagonal entries of the three-state subdivision matrix differ
by the displayed obstruction polynomial. -/
theorem higherStateSubdivision_offDiagonalDifference
    {R : Type*} [CommRing R]
    (x₁ x₂ y z₁ z₂ : R) :
    let Q : Matrix (Fin 3) (Fin 3) R := !![1, y, y; y, z₁, y; y, y, z₂]
    let W : Matrix (Fin 3) (Fin 3) R := !![1, 0, 0; 0, x₁, 0; 0, 0, x₂]
    (Q * W * Q) 0 1 - (Q * W * Q) 0 2 =
      y * (x₁ * (z₁ - y) - x₂ * (z₂ - y)) := by
  dsimp
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- A nonzero obstruction polynomial gives genuinely different off-diagonal
entries, so the common-off-diagonal three-state matrix shape is not preserved. -/
theorem higherStateSubdivision_offDiagonal_ne
    {R : Type*} [CommRing R]
    (x₁ x₂ y z₁ z₂ : R)
    (h : y * (x₁ * (z₁ - y) - x₂ * (z₂ - y)) ≠ 0) :
    let Q : Matrix (Fin 3) (Fin 3) R := !![1, y, y; y, z₁, y; y, y, z₂]
    let W : Matrix (Fin 3) (Fin 3) R := !![1, 0, 0; 0, x₁, 0; 0, 0, x₂]
    (Q * W * Q) 0 1 ≠ (Q * W * Q) 0 2 := by
  dsimp
  intro heq
  apply h
  calc
    y * (x₁ * (z₁ - y) - x₂ * (z₂ - y)) =
        ((!![1, y, y; y, z₁, y; y, y, z₂] : Matrix (Fin 3) (Fin 3) R) *
          !![1, 0, 0; 0, x₁, 0; 0, 0, x₂] *
          !![1, y, y; y, z₁, y; y, y, z₂]) 0 1 -
        ((!![1, y, y; y, z₁, y; y, y, z₂] : Matrix (Fin 3) (Fin 3) R) *
          !![1, 0, 0; 0, x₁, 0; 0, 0, x₂] *
          !![1, y, y; y, z₁, y; y, y, z₂]) 0 2 := by
          simp [Matrix.mul_apply, Fin.sum_univ_three]
          ring
    _ = 0 := sub_eq_zero.mpr heq

end MathlibPlus.Combinatorics.Claim46289

namespace MathlibPlus.Combinatorics.Claim45225

/-- A one-step equality-preserving transformation preserves equality at every
iterate.  The edge-subdivision application supplies `step` from its transfer
identity. -/
theorem equalityPreservedUnderIterate
    {α β : Type*} (G : α → β) (S : α → α) {T T' : α}
    (step : ∀ {U U'}, G U = G U' → G (S U) = G (S U'))
    (h : G T = G T') (k : ℕ) :
    G (S^[k] T) = G (S^[k] T') := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simpa [Function.iterate_succ_apply'] using step ih

end MathlibPlus.Combinatorics.Claim45225
