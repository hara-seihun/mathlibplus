import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

noncomputable section

/-- The uniform auxiliary bounds used inside one variable-width step.  The
strip is expressed by the actual zeta zero and the classical-region
boundary, while the detector parameter is the prescribed
`σ = 1 - A / log (16 t + 10^10)`. -/
def claim1015 : Prop :=
  let A₀ : ℝ := 1 / 4.8594
  let H : ℝ := 3 * 10 ^ 12
  let ε : ℝ := 10 ^ (-100 : ℤ)
  (∀ A δ : ℝ,
      1 / 6 < A →
      A < A₀ →
      0 < δ →
      δ ≤ ε →
      A + δ ≤ A₀ →
      (∀ t : ℝ, H ≤ t →
        ∀ σ : ℝ,
          σ > 1 - A / Real.log t →
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) →
      ∀ t β L : ℝ,
        H ≤ t →
        t ≤ Real.exp 56.693 →
        Real.log H ≤ L →
        L ≤ 56.693 →
        Real.log t = L →
        1 - (A + δ) / Real.log t < β →
        riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I) = 0 →
        let η : ℝ := 1 - β
        let σ : ℝ := 1 - A / Real.log (16 * t + 10 ^ 10)
        let μ : ℝ := (1 - σ) / η
        A ≤ η * Real.log t ∧
          η * Real.log t < A + δ ∧
          μ >
            (A / (A + δ)) *
              (Real.log t / Real.log (16 * t + 10 ^ 10)) ∧
          μ > 1 - 2.78 / L ∧
          η > 1 / (6 * L)) ∧
    (∀ A δ : ℝ,
      1 / 6 < A →
      A < A₀ →
      0 < δ →
      δ ≤ ε →
      A + δ ≤ A₀ →
      (A / (A + δ)) *
          (56.693 / Real.log (16 * Real.exp 56.693 + 10 ^ 10)) -
          (1 - 2.78 / 56.693) > 0.0024)

end
end MathlibPlus.Open.AnalyticNumberTheory
