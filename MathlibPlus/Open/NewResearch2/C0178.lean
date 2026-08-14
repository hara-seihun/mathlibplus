import Mathlib

namespace MathlibPlus.Open.NewResearch2.C0178

noncomputable section

private def l2Norm (f : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x : ℝ, (f x) ^ 2)

private def endpointKernelRegime
    (c A : ℕ → ℝ) (k : ℕ → ℝ → ℝ) : Prop :=
  Filter.Tendsto c Filter.atTop Filter.atTop ∧
    (∀ n, 1 ≤ A n ∧ A n < Real.log (c n)) ∧
    (∀ n, ContDiff ℝ ⊤ (k n) ∧
      ∀ x : ℝ, x < 0 ∨ A n ≤ x → k n x = 0) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        Real.rpow (c n) (-(5 : ℝ) / 4 - ε) ≤ l2Norm (k n) ∧
          l2Norm (k n) ≤ Real.rpow (c n) (-(5 : ℝ) / 4 + ε))

/-- The full-logarithmic endpoint regime is represented by its exact support,
    smoothness, and two-sided meaning of the stated `o(1)` exponent. -/
def fullLogarithmicEndpointKernelRegime_claim2669 : Prop :=
  ∃ (c A : ℕ → ℝ) (k : ℕ → ℝ → ℝ),
    endpointKernelRegime c A k

end
end MathlibPlus.Open.NewResearch2.C0178
