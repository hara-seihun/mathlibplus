import MathlibPlus.Open.ResearchFormalizationBatch_CarryChebyshev

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_CarryChebyshev.O0041Claim10551

noncomputable section

/-- A finite tensor of the actual normalized divisible-base carry matrices is
again the uniform rank-one projector onto the constant tensor state. -/
def claim10551 : Prop :=
  ∀ (r : ℕ) (m : Fin r → ℕ) (b : ℕ),
    2 ≤ b →
      (∀ i : Fin r, 2 ≤ m i ∧ m i ∣ b) →
        let I := ∀ i : Fin r, Fin (m i)
        let T : Matrix I I ℝ :=
          fun c k => ∏ i : Fin r, P (m i) b (c i) (k i)
        (∀ i : Fin r, ∀ c k : Fin (m i),
            P (m i) b c k = (1 : ℝ) / (m i : ℝ)) ∧
          (∀ i : Fin r, (P (m i) b) * (P (m i) b) = P (m i) b) ∧
          (∀ c k : I,
            T c k = (∏ i : Fin r, (m i : ℝ))⁻¹) ∧
          T * T = T ∧
          (∃ c k : I, T c k ≠ 0) ∧
          (∀ c₁ c₂ k₁ k₂ : I,
            T c₁ k₁ * T c₂ k₂ = T c₁ k₂ * T c₂ k₁) ∧
          (∀ x : I → ℝ, ∃ a : ℝ, ∀ c : I, (Matrix.mulVec T x) c = a) ∧
          (∀ a : ℝ, Matrix.mulVec T (fun _ : I => a) = fun _ : I => a)

end

end MathlibPlus.Open.ResearchFormalizationBatch_CarryChebyshev.O0041Claim10551
