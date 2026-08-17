import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch_01a004d6

namespace MathlibPlus.Open.Research.FormalizationBatch.R2003FixedSpectrumConsequence

noncomputable section

open MathlibPlus.Open.Research.FormalizationBatch

/-- The exact fixed-spectrum factor in the admitted sunflower bound. -/
def fixedSpectrumFactor (L : Finset ℕ) (n : ℕ) : ℝ :=
  (8 : ℝ) ^ (L.card - 1) *
    Real.rpow (2 : ℝ)
      (((1 : ℝ) + Real.sqrt 5 / 5) * (n : ℝ) *
        ((L.card - 1 : ℕ) : ℝ))

/-- A base depending only on the finite spectrum, not on the ambient set. -/
def fixedSpectrumBase (L : Finset ℕ) : ℝ :=
  max 1
    ((8 : ℝ) ^ (L.card - 1) *
      Real.rpow (2 : ℝ)
        (((1 : ℝ) + Real.sqrt 5 / 5) *
          ((L.card - 1 : ℕ) : ℝ)))

/-- Claim 35173: for every fixed finite intersection spectrum, the exact
factor has an ambient-independent constant exponential base, and the full
fixed-spectrum family bound retains its polynomial factor. -/
def claim35173 : Prop :=
  ∀ (L : Finset ℕ),
    ∃ C_L : ℝ,
      C_L = fixedSpectrumBase L ∧
      1 ≤ C_L ∧
      (∀ n : ℕ, 1 ≤ n → fixedSpectrumFactor L n ≤ C_L ^ n) ∧
      (∀ {α : Type*} [DecidableEq α]
        (n : ℕ) (F : Finset (Finset α)),
        claim35168_exactFixedIntersectionSpectrum α n L.card L F →
          (F.card : ℝ) ≤
              ((n ^ 2 - n + 2 : ℕ) : ℝ) * fixedSpectrumFactor L n ∧
            (F.card : ℝ) ≤
              ((n ^ 2 - n + 2 : ℕ) : ℝ) * C_L ^ n)

end

end MathlibPlus.Open.Research.FormalizationBatch.R2003FixedSpectrumConsequence
