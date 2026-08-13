import Mathlib

namespace MathlibPlus.Combinatorics

/-- Direct products on disjoint grounds preserve three-sunflower-freeness for
uniform families.  This records the set-theoretic product core of claim 16289;
the later entropy comparison is not part of this theorem. -/
theorem directProduct_threeSunflowerFree_claim16289
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (m n : ℕ)
    (𝓐 : Finset (Finset α)) (𝓑 : Finset (Finset β))
    (hAuniform : ∀ A ∈ 𝓐, A.card = m)
    (hBuniform : ∀ B ∈ 𝓑, B.card = n)
    (hAfree : ∀ A₁ A₂ A₃ : Finset α,
      A₁ ∈ 𝓐 → A₂ ∈ 𝓐 → A₃ ∈ 𝓐 →
      A₁ ≠ A₂ → A₁ ≠ A₃ → A₂ ≠ A₃ →
      ¬ (A₁ ∩ A₂ = A₁ ∩ A₃ ∧ A₁ ∩ A₂ = A₂ ∩ A₃))
    (hBfree : ∀ B₁ B₂ B₃ : Finset β,
      B₁ ∈ 𝓑 → B₂ ∈ 𝓑 → B₃ ∈ 𝓑 →
      B₁ ≠ B₂ → B₁ ≠ B₃ → B₂ ≠ B₃ →
      ¬ (B₁ ∩ B₂ = B₁ ∩ B₃ ∧ B₁ ∩ B₂ = B₂ ∩ B₃)) :
    let left : Finset α → Finset (Sum α β) := fun A => A.image Sum.inl
    let right : Finset β → Finset (Sum α β) := fun B => B.image Sum.inr
    let product : Finset α → Finset β → Finset (Sum α β) :=
      fun A B => left A ∪ right B
    ∀ A₁ A₂ A₃ : Finset α, ∀ B₁ B₂ B₃ : Finset β,
      A₁ ∈ 𝓐 → A₂ ∈ 𝓐 → A₃ ∈ 𝓐 →
      B₁ ∈ 𝓑 → B₂ ∈ 𝓑 → B₃ ∈ 𝓑 →
      product A₁ B₁ ≠ product A₂ B₂ →
      product A₁ B₁ ≠ product A₃ B₃ →
      product A₂ B₂ ≠ product A₃ B₃ →
      ¬ (product A₁ B₁ ∩ product A₂ B₂ =
          product A₁ B₁ ∩ product A₃ B₃ ∧
        product A₁ B₁ ∩ product A₂ B₂ =
          product A₂ B₂ ∩ product A₃ B₃) := by
  dsimp
  let left : Finset α → Finset (Sum α β) := fun A => A.image Sum.inl
  let right : Finset β → Finset (Sum α β) := fun B => B.image Sum.inr
  let product : Finset α → Finset β → Finset (Sum α β) :=
    fun A B => left A ∪ right B
  intro A₁ A₂ A₃ B₁ B₂ B₃ hA₁ hA₂ hA₃ hB₁ hB₂ hB₃ hprod12 hprod13 hprod23 hsun
  have hA12_13 : A₁ ∩ A₂ = A₁ ∩ A₃ := by
    apply Finset.ext
    intro a
    have h := congrArg (fun S : Finset (Sum α β) => Sum.inl a ∈ S) hsun.1
    simpa [product, left, right] using h
  have hA12_23 : A₁ ∩ A₂ = A₂ ∩ A₃ := by
    apply Finset.ext
    intro a
    have h := congrArg (fun S : Finset (Sum α β) => Sum.inl a ∈ S) hsun.2
    simpa [product, left, right] using h
  have hB12_13 : B₁ ∩ B₂ = B₁ ∩ B₃ := by
    apply Finset.ext
    intro b
    have h := congrArg (fun S : Finset (Sum α β) => Sum.inr b ∈ S) hsun.1
    simpa [product, left, right] using h
  have hB12_23 : B₁ ∩ B₂ = B₂ ∩ B₃ := by
    apply Finset.ext
    intro b
    have h := congrArg (fun S : Finset (Sum α β) => Sum.inr b ∈ S) hsun.2
    simpa [product, left, right] using h
  by_cases hA₁₂ : A₁ = A₂
  · have hsub : A₁ ⊆ A₃ := by
      intro a ha
      have ha12 : a ∈ A₁ ∩ A₂ := by
        apply Finset.mem_inter.mpr
        exact ⟨ha, by simpa [hA₁₂] using ha⟩
      have ha13 : a ∈ A₁ ∩ A₃ := hA12_13 ▸ ha12
      exact (Finset.mem_inter.mp ha13).2
    have hA₁₃ : A₁ = A₃ := by
      exact Finset.eq_of_subset_of_card_le hsub (by
        rw [hAuniform A₃ hA₃, hAuniform A₁ hA₁])
    have hB₁₂ : B₁ ≠ B₂ := by
      intro h
      apply hprod12
      cases hA₁₂
      cases h
      rfl
    have hB₁₃ : B₁ ≠ B₃ := by
      intro h
      apply hprod13
      cases hA₁₃
      cases h
      rfl
    have hB₂₃ : B₂ ≠ B₃ := by
      intro h
      apply hprod23
      cases hA₁₂
      cases hA₁₃
      cases h
      rfl
    exact hBfree B₁ B₂ B₃ hB₁ hB₂ hB₃ hB₁₂ hB₁₃ hB₂₃
      ⟨hB12_13, hB12_23⟩
  · have hA₁₃ : A₁ ≠ A₃ := by
      intro h
      have hsub : A₁ ⊆ A₂ := by
        intro a ha
        have ha13 : a ∈ A₁ ∩ A₃ := by
          apply Finset.mem_inter.mpr
          exact ⟨ha, by simpa [h] using ha⟩
        have ha12 : a ∈ A₁ ∩ A₂ := hA12_13.symm ▸ ha13
        exact (Finset.mem_inter.mp ha12).2
      have heq : A₁ = A₂ := by
        exact Finset.eq_of_subset_of_card_le hsub (by
          rw [hAuniform A₂ hA₂, hAuniform A₁ hA₁])
      exact hA₁₂ heq
    have hA₂₃ : A₂ ≠ A₃ := by
      intro h
      have hsub : A₂ ⊆ A₁ := by
        intro a ha
        have ha23 : a ∈ A₂ ∩ A₃ := by
          apply Finset.mem_inter.mpr
          exact ⟨ha, by simpa [h] using ha⟩
        have ha12 : a ∈ A₁ ∩ A₂ := hA12_23.symm ▸ ha23
        exact (Finset.mem_inter.mp ha12).1
      have heq' : A₂ = A₁ := by
        exact Finset.eq_of_subset_of_card_le hsub (by
          rw [hAuniform A₂ hA₂, hAuniform A₁ hA₁])
      exact hA₁₂ heq'.symm
    exact hAfree A₁ A₂ A₃ hA₁ hA₂ hA₃ hA₁₂ hA₁₃ hA₂₃
      ⟨hA12_13, hA12_23⟩

end MathlibPlus.Combinatorics
