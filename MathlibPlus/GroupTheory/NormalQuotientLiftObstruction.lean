import Mathlib

namespace MathlibPlus.GroupTheory

/-- The complete quotient lift on the Klein four-group is invariant under an
ambient automorphism that moves the chosen normal subgroup. -/
theorem completeQuotientLift_doesNotForce_normalSubgroupPreservation :
    let N : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
      (⊤ : Subgroup (Multiplicative (ZMod 2))).prod ⊥
    let U : Set ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ⧸ N) :=
      {q | q ≠ 1}
    let S : Set (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
      (QuotientGroup.mk' N) ⁻¹' U ∪ ((N : Set _) \ {1})
    ∃ α : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)),
      α '' S = S ∧ α '' (N : Set _) ≠ (N : Set _) := by
  dsimp only
  let N : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    (⊤ : Subgroup (Multiplicative (ZMod 2))).prod ⊥
  let U : Set ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ⧸ N) :=
    {q | q ≠ 1}
  let S : Set (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    (QuotientGroup.mk' N) ⁻¹' U ∪ ((N : Set _) \ {1})
  let α : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := MulEquiv.prodComm
  have hS : S = {g | g ≠ 1} := by
    ext g
    simp only [S, U, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff,
      QuotientGroup.mk'_apply]
    have hq :
        ((g : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ⧸ N) ≠ 1) ↔
          g ∉ N := not_congr (QuotientGroup.eq_one_iff g)
    rw [hq]
    constructor
    · rintro (hg | ⟨-, hg⟩)
      · intro hgone
        subst g
        exact hg N.one_mem
      · exact hg
    · intro hg
      by_cases hgN : g ∈ N
      · exact Or.inr ⟨hgN, hg⟩
      · exact Or.inl hgN
  refine ⟨α, ?_, ?_⟩
  · change α '' S = S
    rw [hS]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      refine ⟨α.symm y, ?_, by simp⟩
      simpa using hy
  · change α '' (N : Set _) ≠ (N : Set _)
    let a : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
    have ha : a ≠ 1 := by
      norm_num [a]
    intro hEq
    have hxN : (a, 1) ∈ N :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩
    have himg : α (a, 1) ∈ α '' (N : Set _) := ⟨(a, 1), hxN, rfl⟩
    rw [hEq] at himg
    have himg' : (1, a) ∈ N := by simpa [α] using himg
    have ha_bot : a ∈ (⊥ : Subgroup (Multiplicative (ZMod 2))) :=
      (Subgroup.mem_prod.mp himg').2
    exact ha (Subgroup.mem_bot.mp ha_bot)

end MathlibPlus.GroupTheory
