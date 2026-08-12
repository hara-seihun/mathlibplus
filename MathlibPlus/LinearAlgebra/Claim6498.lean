import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Ring

namespace MathlibPlus.LinearAlgebra.Claim6498

/-- Coordinate form of the canonical Gale tensor relation.

The columns are labelled by `Fin b ⊕ Fin a`; `D` is `[I_b | X]` and `U` is
`[-Xᵀ | I_a]`.  The displayed coordinate sum is the `(r,s)` coordinate of
`∑ᵢ uᵢ ⊗ dᵢ`. -/
theorem canonicalGale_tensorRelation
    {F : Type*} [Field F] {a b : ℕ}
    (X : Matrix (Fin a) (Fin b) F) :
    let D : Matrix (Fin b) (Fin b ⊕ Fin a) F := fun s i =>
      match i with
      | Sum.inl j => if s = j then 1 else 0
      | Sum.inr k => X k s
    let U : Matrix (Fin a) (Fin b ⊕ Fin a) F := fun r i =>
      match i with
      | Sum.inl j => -X r j
      | Sum.inr k => if r = k then 1 else 0
    ∀ r s, ∑ i, U r i * D s i = 0 := by
  dsimp
  intro r s
  classical
  rw [Fintype.sum_sum_type]
  change
    (∑ j : Fin b, -X r j * (if s = j then 1 else 0)) +
      ∑ k : Fin a, (if r = k then 1 else 0) * X k s = 0
  have hleft :
      (∑ j : Fin b, -X r j * (if s = j then 1 else 0)) = -X r s := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro j _ hjs
      simp [Ne.symm hjs]
    · simp
  have hright :
      (∑ k : Fin a, (if r = k then 1 else 0) * X k s) = X r s := by
    rw [Finset.sum_eq_single r]
    · simp
    · intro k _ hkr
      simp [Ne.symm hkr]
    · simp
  rw [hleft, hright]
  ring

end MathlibPlus.LinearAlgebra.Claim6498
