import Mathlib
namespace MathlibPlus.Combinatorics.Claim5968
open scoped BigOperators
noncomputable section

private lemma interval_alt_sum {α : Type*} [DecidableEq α]
    (S U : Finset α) (hSU : S ⊆ U) :
    (∑ T ∈ U.powerset.filter (S ⊆ ·),
      (-1 : ℤ) ^ (T.card - S.card)) = if U = S then 1 else 0 := by
  classical
  let V := U \ S
  let A := V.powerset
  have hVU : V ⊆ U := by
    intro a ha
    exact (Finset.mem_sdiff.mp ha).1
  have hmap_mem : ∀ W ∈ A, W ∪ S ∈ U.powerset.filter (S ⊆ ·) := by
    intro W hW
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_powerset.mpr (Finset.union_subset
        (Finset.mem_powerset.mp hW |>.trans hVU) hSU)
    · exact Finset.subset_union_right
  have hmap_inj : Set.InjOn (fun W : Finset α => W ∪ S) (↑A : Set (Finset α)) := by
    intro W hW Z hZ h
    have hWsub : W ⊆ V := Finset.mem_powerset.mp hW
    have hZsub : Z ⊆ V := Finset.mem_powerset.mp hZ
    have hWdis : Disjoint W S := (Finset.disjoint_left.2 fun a haW haS =>
      (Finset.mem_sdiff.mp (hWsub haW)).2 haS)
    have hZdis : Disjoint Z S := (Finset.disjoint_left.2 fun a haZ haS =>
      (Finset.mem_sdiff.mp (hZsub haZ)).2 haS)
    have h' := congrArg (fun R : Finset α => R \ S) h
    rw [Finset.union_sdiff_cancel_right hWdis,
      Finset.union_sdiff_cancel_right hZdis] at h'
    exact h'
  have hmap_surj : ∀ T ∈ U.powerset.filter (S ⊆ ·),
      ∃ W ∈ A, W ∪ S = T := by
    intro T hT
    have hTU : T ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.1 hT).1
    have hST : S ⊆ T := Finset.mem_filter.1 hT |>.2
    refine ⟨T \ S, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr (fun a ha =>
        Finset.mem_sdiff.mpr ⟨hTU (Finset.mem_sdiff.1 ha).1,
          (Finset.mem_sdiff.1 ha).2⟩)
    · exact Finset.sdiff_union_of_subset hST
  have hsum :
      (∑ T ∈ U.powerset.filter (S ⊆ ·),
        (-1 : ℤ) ^ (T.card - S.card)) =
      ∑ W ∈ A, (-1 : ℤ) ^ ((W ∪ S).card - S.card) := by
    symm
    apply Finset.sum_bij (s := A)
      (t := U.powerset.filter (S ⊆ ·))
      (f := fun W : Finset α => (-1 : ℤ) ^ ((W ∪ S).card - S.card))
      (g := fun T : Finset α => (-1 : ℤ) ^ (T.card - S.card))
      (fun W _ => W ∪ S) hmap_mem hmap_inj
    intro T hT
    obtain ⟨W, hW, hWT⟩ := hmap_surj T hT
    exact ⟨W, hW, hWT⟩
    intro W hW
    rfl
  rw [hsum]
  calc
    (∑ W ∈ A, (-1 : ℤ) ^ ((W ∪ S).card - S.card)) =
        ∑ W ∈ A, (-1 : ℤ) ^ W.card := by
      apply Finset.sum_congr rfl
      intro W hW
      have hWsub : W ⊆ V := Finset.mem_powerset.1 hW
      have hWS : Disjoint W S := Finset.sdiff_disjoint.mono_left hWsub
      rw [Finset.card_union_of_disjoint hWS]
      simp only [Nat.add_sub_cancel]
    _ = (if V = ∅ then 1 else 0) := Finset.sum_powerset_neg_one_pow_card
    _ = (if U = S then 1 else 0) := by
      have hiff : U \ S = ∅ ↔ U = S := by
        rw [Finset.sdiff_eq_empty_iff_subset]
        constructor
        · intro hUS
          exact Finset.Subset.antisymm hUS hSU
        · intro h
          simpa [h]
      simp only [V, hiff]

private lemma inner_coeff_mul {α : Type*} [DecidableEq α]
    (s S U : Finset α) (hU : U ∈ s.powerset) (xU : ℤ) :
    (∑ T ∈ s.powerset,
      if S ⊆ T then if T ⊆ U then
        (-1 : ℤ) ^ (T.card - S.card) * xU else 0 else 0) =
      xU * (if S ⊆ U then if U = S then 1 else 0 else 0) := by
  classical
  by_cases hSU : S ⊆ U
  · have hUs : U ⊆ s := Finset.mem_powerset.mp hU
    have hfilter :
        (s.powerset.filter (S ⊆ ·)).filter (· ⊆ U) =
          U.powerset.filter (S ⊆ ·) := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨hTs, hST⟩, hTU⟩
        exact ⟨hTU, hST⟩
      · rintro ⟨hTU, hST⟩
        exact ⟨⟨hTU.trans hUs, hST⟩, hTU⟩
    rw [← Finset.sum_filter, ← Finset.sum_filter, hfilter,
      ← Finset.sum_mul, interval_alt_sum S U hSU]
    simp [hSU, mul_comm]
  · calc
      (∑ T ∈ s.powerset,
        if S ⊆ T then if T ⊆ U then
          (-1 : ℤ) ^ (T.card - S.card) * xU else 0 else 0) =
          ∑ T ∈ s.powerset, (0 : ℤ) := by
        apply Finset.sum_congr rfl
        intro T hT
        by_cases hST : S ⊆ T
        · by_cases hTU : T ⊆ U
          · exact (hSU (hST.trans hTU)).elim
          · simp [hST, hTU]
        · simp [hST]
      _ = xU * (if S ⊆ U then if U = S then 1 else 0 else 0) := by simp [hSU]

theorem booleanMobiusRecovery_claim5968 {α : Type*} [DecidableEq α]
    (s : Finset α) (x m : Finset α → ℤ)
    (hm : ∀ T ∈ s.powerset, T.Nonempty →
      m T = ∑ U ∈ s.powerset.filter (T ⊆ ·), x U) :
    ∀ S ∈ s.powerset, S.Nonempty →
      x S = ∑ T ∈ s.powerset.filter (S ⊆ ·),
        (-1 : ℤ) ^ (T.card - S.card) * m T := by
  classical
  intro S hS hSne
  have hexpand :
      (∑ T ∈ s.powerset.filter (S ⊆ ·),
        (-1 : ℤ) ^ (T.card - S.card) * m T) =
      ∑ T ∈ s.powerset, ∑ U ∈ s.powerset,
        if S ⊆ T then if T ⊆ U then
          (-1 : ℤ) ^ (T.card - S.card) * x U else 0 else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hST : S ⊆ T
    · have hTne : T.Nonempty := hSne.mono hST
      rw [if_pos hST, hm T hT hTne, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hTU : T ⊆ U
      · simp [hST, hTU]
      · simp [hST, hTU]
    · simp [hST]
  rw [hexpand, Finset.sum_comm]
  symm
  calc
    (∑ U ∈ s.powerset, ∑ T ∈ s.powerset,
        if S ⊆ T then if T ⊆ U then
          (-1 : ℤ) ^ (T.card - S.card) * x U else 0 else 0) =
      ∑ U ∈ s.powerset, x U *
        (if S ⊆ U then if U = S then 1 else 0 else 0) := by
      apply Finset.sum_congr rfl
      intro U hU
      exact inner_coeff_mul s S U hU (x U)
    _ = x S := by
      have hS_eq : ∀ T ∈ s.powerset,
          x T * (if S ⊆ T then if T = S then 1 else 0 else 0) =
            if T = S then x S else 0 := by
        intro T hT
        by_cases hTS : T = S
        · simp [hTS]
        · by_cases hST : S ⊆ T
          · simp [hTS]
          · simp [hST, hTS]
      have hsum :
          (∑ U ∈ s.powerset, x U *
            (if S ⊆ U then if U = S then 1 else 0 else 0)) =
            ∑ U ∈ s.powerset, if U = S then x S else 0 := by
        apply Finset.sum_congr rfl
        intro U hU
        exact hS_eq U hU
      rw [hsum]
      have hsingle : (s.powerset.filter (fun T => T = S)) = {S} := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · rintro ⟨hTs, rfl⟩
          exact rfl
        · intro hTS
          subst T
          exact ⟨Finset.mem_powerset.mp hS, rfl⟩
      rw [← Finset.sum_filter, hsingle]
      simp

end
end MathlibPlus.Combinatorics.Claim5968
