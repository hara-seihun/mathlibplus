import Mathlib

open scoped Interval
open MeasureTheory
open Set

namespace MathlibPlus.Open.ResearchFormalizationBatch.C0158Claim2467

noncomputable section

/-- The centered transform of the exact first-cell packet is the translated
cosine transform of its logarithmic endpoint kernel. -/
def claim2467_exactTranslatedCosineTransform : Prop :=
  ∀ (B c δ : ℝ),
    1 < B → B < 2 → c > B →
      ∀ (φ : ℝ → ℝ),
        ContDiff ℝ ⊤ φ →
        HasCompactSupport φ →
        Function.support φ ⊆ Ioo (1 : ℝ) B →
          let p : ℝ → ℝ :=
            fun v => δ * Real.sqrt c * φ (c * |v|)
          let kφ : ℝ → ℝ :=
            fun x => Real.exp (x / 2) * φ (Real.exp x)
          let K : ℝ → ℝ :=
            fun x =>
              Real.exp (x / 2) / Real.sqrt c *
                ∑ n ∈ Finset.Icc 1 (Nat.ceil (c * Real.exp (-x))),
                  if (1 : ℝ) ≤ n ∧ (n : ℝ) < c * Real.exp (-x) then
                    p ((n : ℝ) * Real.exp x / c)
                  else 0
          let L : ℝ := Real.log c
          let G : ℂ → ℂ :=
            fun z =>
              ∫ x in (0 : ℝ)..L,
                (K x : ℂ) *
                  Complex.cos (z * ((x - L / 2 : ℝ) : ℂ))
          ∀ z : ℂ,
            G z = (δ : ℂ) *
              ∫ x in (0 : ℝ)..Real.log B,
                (kφ x : ℂ) *
                  Complex.cos
                    (z * ((x - Real.log c / 2 : ℝ) : ℂ))

end

end MathlibPlus.Open.ResearchFormalizationBatch.C0158Claim2467
