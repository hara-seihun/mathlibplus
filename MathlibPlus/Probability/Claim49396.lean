import MathlibPlus.Basic

namespace MathlibPlus.Probability.Claim49396

/-- Exact finite counterexample to the proposed covariance pair payment in claim 49396.
The two displayed Boolean functions share the middle sign, while the proposed
cross-saving roots are the first and third signs respectively. -/
theorem crossSavingsCounterexample_claim49396 :
    let avg : (Bool → Bool → Bool → ℝ) → ℝ :=
      fun f => (1 / 8 : ℝ) *
        ∑ x₀ : Bool, ∑ x₁ : Bool, ∑ x₂ : Bool, f x₀ x₁ x₂
    let h : Bool → Bool → Bool → ℝ :=
      fun x₀ x₁ _x₂ => if x₀ = false ∧ x₁ = true then 1 else -1
    let k : Bool → Bool → Bool → ℝ :=
      fun _x₀ x₁ x₂ => if x₁ = true ∧ x₂ = false then 1 else -1
    let condFirst :
        ((Bool → Bool → Bool → ℝ) → Bool → ℝ) :=
      fun f b => (1 / 4 : ℝ) * ∑ x₁ : Bool, ∑ x₂ : Bool, f b x₁ x₂
    let condThird :
        ((Bool → Bool → Bool → ℝ) → Bool → ℝ) :=
      fun f b => (1 / 4 : ℝ) * ∑ x₀ : Bool, ∑ x₁ : Bool, f x₀ x₁ b
    let savingFirst : (Bool → Bool → Bool → ℝ) → ℝ :=
      fun f => (1 / 2 : ℝ) *
        ∑ b : Bool, (condFirst f b - avg f) ^ 2
    let savingThird : (Bool → Bool → Bool → ℝ) → ℝ :=
      fun f => (1 / 2 : ℝ) *
        ∑ b : Bool, (condThird f b - avg f) ^ 2
    let covariance :
        (Bool → Bool → Bool → ℝ) → (Bool → Bool → Bool → ℝ) → ℝ :=
      fun f g => avg (fun x₀ x₁ x₂ =>
        (f x₀ x₁ x₂ - avg f) * (g x₀ x₁ x₂ - avg g))
    covariance h k = (1 / 4 : ℝ) ∧
      savingFirst k = 0 ∧ savingThird h = 0 ∧
      ¬ (covariance h k ≤ savingFirst k + savingThird h) := by
  dsimp
  norm_num [Fintype.sum_bool]

end MathlibPlus.Probability.Claim49396
