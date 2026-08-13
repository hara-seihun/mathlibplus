import MathlibPlus.Open.Combinatorics.InverseClosedMarkerSpectrum

namespace MathlibPlus.Combinatorics

open scoped Pointwise

private lemma marker_arithmetic (n f q : ℕ) (hf : 0 < f) (hn : n ≤ f + 2*q) :
    ∃ k j : ℕ, k ≤ f ∧ j ≤ q ∧ k + 2*j = n := by
  by_cases hnf : n ≤ f
  · exact ⟨n, 0, hnf, by omega, by omega⟩
  · have hfn : f < n := by omega
    rcases Nat.mod_two_eq_zero_or_one (n - f) with heven | hodd
    · let j := (n - f) / 2
      have hdiv := Nat.div_add_mod (n - f) 2
      refine ⟨f, j, by omega, ?_, ?_⟩
      · dsimp [j]
        omega
      · dsimp [j]
        omega
    · let j := (n - f) / 2 + 1
      have hdiv := Nat.div_add_mod (n - f) 2
      refine ⟨f - 1, j, by omega, ?_, ?_⟩
      · dsimp [j]
        omega
      · dsimp [j]
        omega

/-- Every finite group has inverse-closed subsets of every cardinality. -/
theorem inverseClosedMarkerSpectrum :
    MathlibPlus.Open.Combinatorics.inverseClosedMarkerSpectrum := by
  intro G _ _ n hn
  letI := Fintype.ofFinite G
  classical
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let fixed : Finset G := Finset.univ.filter fun x => x⁻¹ = x
  let reps : Finset G := Finset.univ.filter fun x => e x < e x⁻¹
  have hfixed_pos : 0 < fixed.card := by
    rw [Finset.card_pos]
    refine ⟨1, ?_⟩
    simp [fixed]
  have hfixed_reps : Disjoint fixed reps := by
    rw [Finset.disjoint_left]
    intro x hxf hxr
    simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hxf
    simp only [reps, Finset.mem_filter, Finset.mem_univ, true_and] at hxr
    rw [hxf] at hxr
    exact (lt_irrefl _ hxr)
  have hfixed_invReps : Disjoint fixed reps⁻¹ := by
    rw [Finset.disjoint_left]
    intro x hxf hxr
    simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hxf
    rw [Finset.mem_inv] at hxr
    obtain ⟨y, hyr, hyx⟩ := hxr
    simp only [reps, Finset.mem_filter, Finset.mem_univ, true_and] at hyr
    subst x
    rw [inv_inv] at hxf
    rw [← hxf] at hyr
    exact (lt_irrefl _ hyr)
  have hreps_invReps : Disjoint reps reps⁻¹ := by
    rw [Finset.disjoint_left]
    intro x hxr hxri
    simp only [reps, Finset.mem_filter, Finset.mem_univ, true_and] at hxr
    rw [Finset.mem_inv] at hxri
    obtain ⟨y, hyr, hyx⟩ := hxri
    simp only [reps, Finset.mem_filter, Finset.mem_univ, true_and] at hyr
    subst x
    rw [inv_inv] at hxr
    exact (not_lt_of_ge (le_of_lt hyr) hxr)
  have hpartition : fixed ∪ reps ∪ reps⁻¹ = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inv, Finset.mem_univ, iff_true]
    by_cases hx : x⁻¹ = x
    · exact Or.inl (Or.inl (by simp [fixed, hx]))
    · rcases lt_trichotomy (e x) (e x⁻¹) with hlt | heq | hgt
      · exact Or.inl (Or.inr (by simp [reps, hlt]))
      · exact False.elim (hx (e.injective heq.symm))
      · exact Or.inr ⟨x⁻¹, by simp [reps, hgt]⟩
  have huniv_card : Fintype.card G = fixed.card + 2 * reps.card := by
    rw [← Finset.card_univ, ← hpartition]
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_union_of_disjoint hfixed_reps, Finset.card_inv]
      omega
    · exact Finset.disjoint_union_left.mpr ⟨hfixed_invReps, hreps_invReps⟩
  have hn' : n ≤ fixed.card + 2 * reps.card := by
    rw [← huniv_card, ← Nat.card_eq_fintype_card]
    exact hn
  obtain ⟨k, j, hk, hj, hkj⟩ := marker_arithmetic n fixed.card reps.card hfixed_pos hn'
  obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq hk
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hj
  let S : Finset G := K ∪ J ∪ J⁻¹
  refine ⟨S, ?_, ?_⟩
  · intro x
    have hKfixed : ∀ y ∈ K, y⁻¹ = y := by
      intro y hy
      have := hKsub hy
      simpa [fixed] using this
    simp only [S, Finset.mem_union, Finset.mem_inv]
    constructor
    · rintro ((hxK | hxJ) | ⟨y, hyJ, hyx⟩)
      · exact Or.inl (Or.inl (by simpa [hKfixed x hxK] using hxK))
      · exact Or.inr ⟨x, hxJ, rfl⟩
      · subst x
        rw [inv_inv]
        exact Or.inl (Or.inr hyJ)
    · rintro ((hxiK | hxiJ) | ⟨y, hyJ, hyx⟩)
      · have hxinv := hKfixed x⁻¹ hxiK
        rw [inv_inv] at hxinv
        exact Or.inl (Or.inl (by simpa [← hxinv] using hxiK))
      · exact Or.inr ⟨x⁻¹, hxiJ, inv_inv x⟩
      · rw [inv_inj] at hyx
        subst y
        exact Or.inl (Or.inr hyJ)
  · have hKJ : Disjoint K J := hfixed_reps.mono hKsub hJsub
    have hKJinv : Disjoint K J⁻¹ := by
      apply hfixed_invReps.mono hKsub
      intro x hx
      rw [Finset.mem_inv] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hJsub hy, rfl⟩
    have hJJinv : Disjoint J J⁻¹ := by
      apply hreps_invReps.mono hJsub
      intro x hx
      rw [Finset.mem_inv] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hJsub hy, rfl⟩
    dsimp [S]
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_union_of_disjoint hKJ, Finset.card_inv, hKcard, hJcard]
      omega
    · exact Finset.disjoint_union_left.mpr ⟨hKJinv, hJJinv⟩

end MathlibPlus.Combinatorics
