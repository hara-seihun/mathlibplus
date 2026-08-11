import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory.Claim53256

/-- A common multiplicative context distributes over every pair sum. -/
theorem commonContext_pairSum_claim53256
    {R : Type*} [Semiring R] (H Aᵢ Aⱼ : R) :
    H * Aᵢ + H * Aⱼ = H * (Aᵢ + Aⱼ) := by
  rw [mul_add]

/-- Adding one common integer to six valuation coordinates preserves their
minimum and the strict-above-minimum matching set. -/
theorem commonContext_sixMatchingSet_claim53256
    (v : Fin 6 → ℤ) (c e : ℤ)
    (hmin : ∀ i, e ≤ v i)
    (hattain : ∃ i, v i = e) :
    (∀ i, c + e ≤ c + v i) ∧
      (∃ i, c + v i = c + e) ∧
      (∀ i, c + v i > c + e ↔ v i > e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    linarith [hmin i]
  · rcases hattain with ⟨i, hi⟩
    exact ⟨i, by linarith⟩
  · intro i
    constructor <;> intro hi <;> linarith

end MathlibPlus.NumberTheory.Claim53256
