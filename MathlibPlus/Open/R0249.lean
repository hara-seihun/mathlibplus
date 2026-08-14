import Mathlib

namespace MathlibPlus.Open.R0249

noncomputable section

/-- Deleting the signed bump replaces the signed flux by its positive part. -/
def claim_19183 : Prop :=
  ∀ (φ : ℝ → ℝ), Differentiable ℝ φ →
    let q : ℝ → ℝ := fun x => -deriv φ x
    let qpos : ℝ → ℝ := fun x => max (q x) 0
    let qneg : ℝ → ℝ := fun x => max (-q x) 0
    (q = qpos - qneg) ∧
    (∀ x, 0 ≤ qpos x ∧ 0 ≤ qneg x) ∧
    (∀ x, qpos x = max (-deriv φ x) 0)

end

end MathlibPlus.Open.R0249
