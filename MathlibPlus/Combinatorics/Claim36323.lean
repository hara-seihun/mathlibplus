import Mathlib

namespace MathlibPlus.Combinatorics

/-- The incidence-support criterion for a selected `k`-tuple of a distinct uniform
family.  The selected family is represented by a finset `K`, so distinctness is
built into the representation. -/
theorem literalIncidenceSupport_sunflower_iff_claim36323
    {α : Type*} [Fintype α] [DecidableEq α]
    (n k : ℕ) (F K : Finset (Finset α))
    (huniform : ∀ A ∈ F, A.card = n)
    (hk : 3 ≤ k) (hKF : K ⊆ F) (hKcard : K.card = k) :
    (∃ C : Finset α,
      ∀ A ∈ K, ∀ B ∈ K, A ≠ B → A ∩ B = C) ↔
      ∀ x : α,
        (K.filter (fun A => x ∈ A)).card = 0 ∨
        (K.filter (fun A => x ∈ A)).card = 1 ∨
        (K.filter (fun A => x ∈ A)).card = K.card := by
  classical
  constructor
  · rintro ⟨C, hC⟩ x
    let S := K.filter (fun A => x ∈ A)
    by_cases h0 : S.card = 0
    · exact Or.inl h0
    by_cases h1 : S.card = 1
    · exact Or.inr (Or.inl h1)
    right
    right
    have hSgt : 1 < S.card := by omega
    obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp hSgt
    have hAK : A ∈ K := (Finset.mem_filter.mp hA).1
    have hxA : x ∈ A := (Finset.mem_filter.mp hA).2
    have hBK : B ∈ K := (Finset.mem_filter.mp hB).1
    have hxB : x ∈ B := (Finset.mem_filter.mp hB).2
    have hxC : x ∈ C := by
      rw [← hC A hAK B hBK hAB]
      exact Finset.mem_inter.mpr ⟨hxA, hxB⟩
    have hS : S = K := by
      apply Finset.filter_eq_self.mpr
      intro D hD
      have hxD : x ∈ D := by
        by_cases hDA : D = A
        · simpa [hDA] using hxA
        · have hAD : A ≠ D := Ne.symm hDA
          have hCD : A ∩ D = C := hC A hAK D hD hAD
          have : x ∈ A ∩ D := by simpa [hCD] using hxC
          exact (Finset.mem_inter.mp this).2
      exact hxD
    simpa [S] using congrArg Finset.card hS
  · intro hcriterion
    let C : Finset α := Finset.univ.filter (fun x => ∀ A ∈ K, x ∈ A)
    refine ⟨C, ?_⟩
    intro A hA B hB hAB
    ext x
    constructor
    · intro hx
      have hAS : A ∈ K.filter (fun D => x ∈ D) :=
        Finset.mem_filter.mpr ⟨hA, (Finset.mem_inter.mp hx).1⟩
      have hBS : B ∈ K.filter (fun D => x ∈ D) :=
        Finset.mem_filter.mpr ⟨hB, (Finset.mem_inter.mp hx).2⟩
      have hSgt : 1 < (K.filter (fun D => x ∈ D)).card :=
        Finset.one_lt_card.mpr ⟨A, hAS, B, hBS, hAB⟩
      have hScard : (K.filter (fun D => x ∈ D)).card = K.card := by
        rcases hcriterion x with h0 | h1 | hkcard
        · omega
        · omega
        · exact hkcard
      have hfilter : K.filter (fun D => x ∈ D) = K := by
        apply Finset.eq_of_subset_of_card_le
          (Finset.filter_subset (p := fun D : Finset α => x ∈ D) K)
        simpa [hScard]
      have hxall : ∀ D ∈ K, x ∈ D := by
        intro D hD
        have : D ∈ K.filter (fun E => x ∈ E) := by
          rw [hfilter]
          exact hD
        exact (Finset.mem_filter.mp this).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxall⟩
    · intro hx
      have hxall : ∀ D ∈ K, x ∈ D := (Finset.mem_filter.mp hx).2
      exact Finset.mem_inter.mpr ⟨hxall A hA, hxall B hB⟩

/-- In a `k`-sunflower-free selected `k`-tuple, some coordinate has an
intermediate literal incidence support. -/
theorem sunflowerFree_has_intermediate_support_claim36323
    {α : Type*} [Fintype α] [DecidableEq α]
    (n k : ℕ) (F K : Finset (Finset α))
    (huniform : ∀ A ∈ F, A.card = n)
    (hk : 3 ≤ k) (hKF : K ⊆ F) (hKcard : K.card = k)
    (hFfree : ¬ ∃ K' : Finset (Finset α), K' ⊆ F ∧ K'.card = k ∧
      ∃ C : Finset α,
        ∀ A ∈ K', ∀ B ∈ K', A ≠ B → A ∩ B = C) :
    ∃ x : α,
      2 ≤ (K.filter (fun A => x ∈ A)).card ∧
        (K.filter (fun A => x ∈ A)).card < k := by
  classical
  by_contra hnone
  have hnone' : ∀ x : α, ¬ (2 ≤ (K.filter (fun A => x ∈ A)).card ∧
      (K.filter (fun A => x ∈ A)).card < k) := by
    intro x hx
    exact hnone ⟨x, hx⟩
  have hfree : ¬ ∃ C : Finset α,
      ∀ A ∈ K, ∀ B ∈ K, A ≠ B → A ∩ B = C := by
    intro hC
    exact hFfree ⟨K, hKF, hKcard, hC⟩
  apply hfree
  apply (literalIncidenceSupport_sunflower_iff_claim36323 n k F K huniform hk hKF hKcard).2
  intro x
  by_cases h0 : (K.filter (fun A => x ∈ A)).card = 0
  · exact Or.inl h0
  by_cases h1 : (K.filter (fun A => x ∈ A)).card = 1
  · exact Or.inr (Or.inl h1)
  right
  right
  have hge2 : 2 ≤ (K.filter (fun A => x ∈ A)).card := by omega
  have hnotlt : ¬ (K.filter (fun A => x ∈ A)).card < k := by
    intro hlt
    exact hnone' x ⟨hge2, hlt⟩
  have hle : (K.filter (fun A => x ∈ A)).card ≤ k := by
    simpa [hKcard] using
      Finset.card_le_card (Finset.filter_subset (p := fun A : Finset α => x ∈ A) K)
  omega

end MathlibPlus.Combinatorics
