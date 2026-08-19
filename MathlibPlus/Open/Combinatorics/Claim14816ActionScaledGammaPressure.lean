import MathlibPlus.Open.Combinatorics.NevilleGammaAllHoleClaim14815

open Filter Topology

namespace MathlibPlus.Open.Combinatorics.NevilleGamma

noncomputable section

/-- Claim 14816: the exact all-hole interaction from the gamma--Darboux
Neville carrier has the stated positive action-scaled linear limit whenever
`α_n/n` tends to a positive `κ`. -/
def claim14816 : Prop :=
  ∀ (κ : ℝ), 0 < κ →
    ∀ (α : ℕ → ℝ),
      Tendsto (fun n : ℕ => α n / (n : ℝ)) atTop (𝓝 κ) →
        let limitValue : ℝ :=
          2 * Real.rpow (κ / (1 + κ)) (κ + 1)
        (Tendsto
            (fun n : ℕ =>
              Real.rpow
                (gammaAllHoleInteraction14815 (α n) n)
                (1 / (n : ℝ)) / (n : ℝ))
            atTop (𝓝 limitValue)) ∧
          0 < limitValue

end

end MathlibPlus.Open.Combinatorics.NevilleGamma
