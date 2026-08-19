import Mathlib

namespace MathlibPlus.LinearAlgebra.ThreeTermRelation

/-- Claim 36715: the three displayed lower-invariant vectors are pairwise
linearly independent but satisfy a support-minimal three-term relation. The
last clause records that every nonzero relation has all three coefficients
nonzero, so there is no two-term (binomial) relation. -/
theorem pairwiseIndependentThreeTermRelation :
    let A : Fin 2 → ℚ := ![1, 1]
    let B : Fin 2 → ℚ := ![1, -1]
    let C : Fin 2 → ℚ := ![1, 0]
    LinearIndependent ℚ ![A, B] ∧
      LinearIndependent ℚ ![A, C] ∧
      LinearIndependent ℚ ![B, C] ∧
      A + B - 2 • C = 0 ∧
      ∀ (a b c : ℚ),
        a • A + b • B + c • C = 0 →
          (a = 0 ∧ b = 0 ∧ c = 0) ∨
            (a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) := by
  dsimp
  have hAB :
      LinearIndependent ℚ (![![1, 1], ![1, -1]] : Fin 2 → (Fin 2 → ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg0 := congrFun hg 0
    have hg1 := congrFun hg 1
    fin_cases i <;> simp [Fin.sum_univ_two] at hg0 hg1 ⊢ <;> linarith
  have hAC :
      LinearIndependent ℚ (![![1, 1], ![1, 0]] : Fin 2 → (Fin 2 → ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg0 := congrFun hg 0
    have hg1 := congrFun hg 1
    fin_cases i <;> simp [Fin.sum_univ_two] at hg0 hg1 ⊢ <;> linarith
  have hBC :
      LinearIndependent ℚ (![![1, -1], ![1, 0]] : Fin 2 → (Fin 2 → ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg0 := congrFun hg 0
    have hg1 := congrFun hg 1
    fin_cases i <;> simp [Fin.sum_univ_two] at hg0 hg1 ⊢ <;> linarith
  have hsupport : ∀ (a b c : ℚ),
      a • (![1, 1] : Fin 2 → ℚ) +
          b • (![1, -1] : Fin 2 → ℚ) +
          c • (![1, 0] : Fin 2 → ℚ) = 0 →
        (a = 0 ∧ b = 0 ∧ c = 0) ∨
          (a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) := by
    intro a b c h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    by_cases ha : a = 0
    · left
      have hb : b = 0 := by
        linarith [h1]
      have hc : c = 0 := by
        linarith [h0, h1]
      exact ⟨ha, hb, hc⟩
    · right
      have hb : b ≠ 0 := by
        intro hb
        apply ha
        rw [hb] at h1
        linarith
      have hc : c ≠ 0 := by
        intro hc
        apply ha
        rw [hc] at h0
        linarith [h1]
      exact ⟨ha, hb, hc⟩
  refine ⟨hAB, hAC, hBC, ?_, hsupport⟩
  funext i
  fin_cases i <;> norm_num

end MathlibPlus.LinearAlgebra.ThreeTermRelation
