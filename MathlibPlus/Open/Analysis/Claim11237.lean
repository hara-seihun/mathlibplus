import MathlibPlus.Open.Analysis.Claim11235_11240_11241

namespace MathlibPlus.Open.Analysis.Claim11237

open MathlibPlus.Open.Analysis

/-- Evenness and conjugation reality are preserved by the exact multiplier
`Q_m(z) = 1 + z^(4m)`. -/
def plantedProductSymmetry : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∀ F : ℂ → ℂ,
      (∀ z : ℂ, F (-z) = F z) →
      (∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)) →
      let G : ℂ → ℂ := fun z => F z * qₘ m z
      (∀ z : ℂ, G (-z) = G z) ∧
        (∀ z : ℂ,
          G (starRingEnd ℂ z) = starRingEnd ℂ (G z))

end MathlibPlus.Open.Analysis.Claim11237
