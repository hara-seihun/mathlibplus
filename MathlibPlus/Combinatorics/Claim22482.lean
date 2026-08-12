import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.Claim22482

/-- Exact maximum for the three-variable integer triangle optimizer. -/
theorem triangleOptimizer_claim22482 (A C I : ℕ) :
    let Phi : ℕ → ℕ → ℕ → ℕ := fun A C I =>
      if C ≤ A then C + I / 3
      else if C ≤ A + I then C + (I - (C - A)) / 3
      else A + I
    (∀ t₁ t₂ t₃ : ℕ,
        t₁ ≤ A ∧ t₁ + t₂ ≤ C ∧ t₂ + 3 * t₃ ≤ I →
          t₁ + t₂ + t₃ ≤ Phi A C I) ∧
      (∃ t₁ t₂ t₃ : ℕ,
        t₁ ≤ A ∧ t₁ + t₂ ≤ C ∧ t₂ + 3 * t₃ ≤ I ∧
          t₁ + t₂ + t₃ = Phi A C I) := by
  dsimp
  by_cases hCA : C ≤ A
  · simp only [if_pos hCA]
    constructor
    · intro t₁ t₂ t₃ h
      omega
    · refine ⟨C, 0, I / 3, ?_⟩
      omega
  · by_cases hCsum : C ≤ A + I
    · simp only [if_neg hCA, if_pos hCsum]
      constructor
      · intro t₁ t₂ t₃ h
        omega
      · refine ⟨A, C - A, (I - (C - A)) / 3, ?_⟩
        omega
    · simp only [if_neg hCA, if_neg hCsum]
      constructor
      · intro t₁ t₂ t₃ h
        omega
      · refine ⟨A, I, 0, ?_⟩
        omega

end MathlibPlus.Combinatorics.Claim22482
