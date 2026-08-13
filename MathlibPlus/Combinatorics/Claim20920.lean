import Mathlib

namespace MathlibPlus.Combinatorics.Claim20920

/-- A union product of two nonempty, empty-free families with empty total
intersection cannot have at most two members.  The empty-free hypotheses are
explicit because they are needed for the final contradiction in the source
mechanism. -/
theorem unionProduct_card_gt_two_claim20920
    {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α))
    (hFne : F.Nonempty) (hGne : G.Nonempty)
    (hFclosed : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (hGclosed : ∀ A ∈ G, ∀ B ∈ G, A ∪ B ∈ G)
    (hFempty : ∅ ∉ F) (hGempty : ∅ ∉ G)
    (hFomit : ∀ x : α, ∃ s ∈ F, x ∉ s)
    (hGomit : ∀ x : α, ∃ t ∈ G, x ∉ t) :
    let H : Finset (Finset α) :=
      (F.product G).image (fun p => p.1 ∪ p.2)
    3 ≤ H.card := by
  dsimp
  let H : Finset (Finset α) := (F.product G).image (fun p => p.1 ∪ p.2)
  change 3 ≤ H.card
  have hHne : H.Nonempty := by
    rcases hFne with ⟨s, hs⟩
    rcases hGne with ⟨t, ht⟩
    exact ⟨s ∪ t, by
      exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩⟩
  have hHclosed : ∀ A ∈ H, ∀ B ∈ H, A ∪ B ∈ H := by
    intro A hA B hB
    rcases Finset.mem_image.mp hA with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨q, hq, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hpF, hpG⟩
    rcases Finset.mem_product.mp hq with ⟨hqF, hqG⟩
    refine Finset.mem_image.mpr ⟨(p.1 ∪ q.1, p.2 ∪ q.2),
      Finset.mem_product.mpr ⟨hFclosed _ hpF _ hqF, hGclosed _ hpG _ hqG⟩, ?_⟩
    ext x
    simp [Finset.union_left_comm, Finset.union_comm]
  by_contra hsmall
  have hsmall' : H.card ≤ 2 := by omega
  obtain ⟨P, hP, hPmin⟩ := Finset.exists_min_image H (fun s : Finset α => s.card) hHne
  have hPall : ∀ Q ∈ H, P ⊆ Q := by
    intro Q hQ
    by_contra hPQ
    have hQP : ¬ Q ⊆ P := by
      intro hQP
      have hQPss : Q ⊂ P := Finset.ssubset_iff_subset_ne.mpr ⟨hQP, by
        intro hEQ
        apply hPQ
        simp [hEQ]⟩
      have hcardlt : Q.card < P.card := Finset.card_lt_card hQPss
      exact (not_lt_of_ge (hPmin Q hQ)) hcardlt
    have hU : P ∪ Q ∈ H := hHclosed P hP Q hQ
    have hsub : ({P, Q, P ∪ Q} : Finset (Finset α)) ⊆ H := by
      intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      exact hR.elim (fun h => h ▸ hP) (fun h => h.elim (fun h => h ▸ hQ) (fun h => h ▸ hU))
    have hPQne : P ≠ Q := by
      intro hEq
      exact hPQ (hEq ▸ Finset.Subset.rfl)
    have hUPne : P ∪ Q ≠ P := by
      intro hEq
      apply hQP
      intro x hx
      have : x ∈ P ∪ Q := Finset.mem_union_right P hx
      simpa [hEq] using this
    have hUQne : P ∪ Q ≠ Q := by
      intro hEq
      apply hPQ
      intro x hx
      have : x ∈ P ∪ Q := Finset.mem_union_left Q hx
      simpa [hEq] using this
    have hcardK : ({P, Q, P ∪ Q} : Finset (Finset α)).card ≤ H.card :=
      Finset.card_le_card hsub
    have hcardKeq : ({P, Q, P ∪ Q} : Finset (Finset α)).card = 3 := by
      have hPnot : P ∉ ({Q, P ∪ Q} : Finset (Finset α)) := by
        simp [hPQne, hUPne.symm]
      have hQnot : Q ∉ ({P ∪ Q} : Finset (Finset α)) := by
        simp [hUQne.symm]
      rw [Finset.card_insert_of_notMem hPnot,
        Finset.card_insert_of_notMem hQnot]
      simp
    rw [hcardKeq] at hcardK
    omega
  have hPempty : P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases hFomit x with ⟨s, hsF, hxs⟩
    rcases hGomit x with ⟨t, htG, hxt⟩
    have hst : s ∪ t ∈ H := by
      exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hsF, htG⟩, rfl⟩
    have hsub := hPall (s ∪ t) hst
    have hxu : x ∈ s ∪ t := hsub hx
    simp only [Finset.mem_union] at hxu
    exact hxu.elim hxs hxt
  rcases Finset.mem_image.mp hP with ⟨⟨s, t⟩, hst, hUnion⟩
  have hst' : s ∪ t = ∅ := by simpa [hPempty] using hUnion
  have hsEmpty : s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have : x ∈ s ∪ t := Finset.mem_union_left t hx
    rw [hst'] at this
    simp at this
  have hsF : s ∈ F := (Finset.mem_product.mp hst).1
  apply hFempty
  simpa [hsEmpty] using hsF

end MathlibPlus.Combinatorics.Claim20920
