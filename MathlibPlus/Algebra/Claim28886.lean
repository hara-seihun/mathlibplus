import MathlibPlus.Algebra.ClaimIdentities
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace MathlibPlus.Algebra.Claim28886

open scoped LinearAlgebra.Projectivization

/-- The four one-dimensional subspaces of the two-dimensional vector space over
`𝔽₃`, represented by the points of its projectivization. -/
theorem projectiveLineCountF3 :
    Nat.card (ℙ (ZMod 3) (Fin 2 → ZMod 3)) = 4 := by
  rw [Projectivization.card_of_finrank_two (ZMod 3) (Fin 2 → ZMod 3)
    (by simp)]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

/-- The ordered linearly independent pairs in `𝔽₃³` have cardinality
`(27 - 1) * (27 - 3) = 624`. -/
theorem orderedLinearlyIndependentPairsF3 :
    Nat.card
        {p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) //
          LinearIndependent (ZMod 3) ![p.1, p.2]} = 624 := by
  classical
  let e :
      {p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) //
          LinearIndependent (ZMod 3) ![p.1, p.2]} ≃
        {p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) //
          p.2 ≠ 0 ∧ ∀ a : ZMod 3, a • p.2 ≠ p.1} :=
    { toFun := fun p =>
        ⟨p.1, (MathlibPlus.Algebra.ClaimIdentities.orderedIndependentPairsF3_iff p.1).mp p.2⟩
      invFun := fun p =>
        ⟨p.1, (MathlibPlus.Algebra.ClaimIdentities.orderedIndependentPairsF3_iff p.1).mpr p.2⟩
      left_inv := by
        intro p
        cases p
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  calc
    Nat.card
          {p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) //
            LinearIndependent (ZMod 3) ![p.1, p.2]} =
        Nat.card
          {p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) //
            p.2 ≠ 0 ∧ ∀ a : ZMod 3, a • p.2 ≠ p.1} :=
      Nat.card_congr e
    _ = Fintype.card
          {p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) //
            p.2 ≠ 0 ∧ ∀ a : ZMod 3, a • p.2 ≠ p.1} := by
      rw [Nat.card_eq_fintype_card]
    _ = (3 ^ 3 - 1) * (3 ^ 3 - 3) :=
      (MathlibPlus.Algebra.ClaimIdentities.orderedIndependentPairsF3).1
    _ = 624 := by norm_num

end MathlibPlus.Algebra.Claim28886
