import Mathlib

namespace MathlibPlus.Open.Analysis.Moment

noncomputable def twoAtomMoment (w L : ℝ) (k : ℕ) : ℝ :=
  1 + w * L ^ k

noncomputable def twoAtomR (w L : ℝ) : ℝ :=
  (twoAtomMoment w L 1) ^ 2 /
    (twoAtomMoment w L 0 * twoAtomMoment w L 2)

noncomputable def twoAtomS (w L : ℝ) : ℝ :=
  twoAtomMoment w L 1 * twoAtomMoment w L 3 /
    (twoAtomMoment w L 2) ^ 2

noncomputable def twoAtomQ (w L : ℝ) : ℝ :=
  3 * twoAtomS w L + 15 * twoAtomR w L - 10

noncomputable def twoAtomRThresholdSharpness : Prop :=
  (∀ u : ℝ, 0 < u →
    Filter.Tendsto (fun L : ℝ => twoAtomR u L) Filter.atTop
        (nhds (u / (1 + u))) ∧
    Filter.Tendsto (fun L : ℝ => twoAtomS u L) Filter.atTop
        (nhds 1) ∧
    Filter.Tendsto (fun L : ℝ => twoAtomQ u L) Filter.atTop
        (nhds (15 * u / (1 + u) - 7))) ∧
  (∀ u : ℝ, 0 < u → u < (7 : ℝ) / 8 →
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        twoAtomQ u L < 0 ∧
        1 ≤ twoAtomS u L ∧
        twoAtomR u L < (7 : ℝ) / 15) ∧
  Filter.Tendsto (fun u : ℝ => u / (1 + u))
      (nhdsWithin ((7 : ℝ) / 8) (Set.Iio ((7 : ℝ) / 8)))
      (nhds ((7 : ℝ) / 15)) ∧
  ∀ ρ : ℝ, ρ < (7 : ℝ) / 15 →
    ∃ u L : ℝ,
      0 < u ∧ u < (7 : ℝ) / 8 ∧ 0 < L ∧
      ρ < twoAtomR u L ∧
      twoAtomR u L < (7 : ℝ) / 15 ∧
      1 ≤ twoAtomS u L ∧
      twoAtomQ u L < 0

noncomputable def twoAtomSThresholdSharpness : Prop :=
  (∀ u : ℝ, 0 < u →
    Filter.Tendsto (fun L : ℝ => twoAtomR (u / L) L) Filter.atTop
        (nhds 0) ∧
    Filter.Tendsto (fun L : ℝ => twoAtomS (u / L) L) Filter.atTop
        (nhds (1 + 1 / u)) ∧
    Filter.Tendsto (fun L : ℝ => twoAtomQ (u / L) L) Filter.atTop
        (nhds ((3 - 7 * u) / u))) ∧
  (∀ u : ℝ, (3 : ℝ) / 7 < u →
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        twoAtomQ (u / L) L < 0 ∧
        0 < twoAtomR (u / L) L ∧
        twoAtomS (u / L) L < (10 : ℝ) / 3) ∧
  Filter.Tendsto (fun u : ℝ => 1 + 1 / u)
      (nhdsWithin ((3 : ℝ) / 7) (Set.Ioi ((3 : ℝ) / 7)))
      (nhds ((10 : ℝ) / 3)) ∧
  ∀ σ : ℝ, σ < (10 : ℝ) / 3 →
    ∃ u L : ℝ,
      (3 : ℝ) / 7 < u ∧ 0 < L ∧
      σ < twoAtomS (u / L) L ∧
      twoAtomS (u / L) L < (10 : ℝ) / 3 ∧
      0 < twoAtomR (u / L) L ∧
      twoAtomQ (u / L) L < 0

end MathlibPlus.Open.Analysis.Moment
