import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationAuxiliary

noncomputable def auxiliaryG (L h : ℝ) : ℝ :=
  (2 * L ^ 2 / (L + h)) *
    Real.log ((L + Real.log L + 2 * h) / (L - Real.log L))

noncomputable def auxiliaryF (L B h : ℝ) : ℝ :=
  auxiliaryG L h - B * Real.exp h * L ^ 2 / (L + h) ^ 2

def auxiliaryInterval (L : ℝ) : Set ℝ :=
  Set.Ioo (-Real.log L) (L - 2 * Real.log L)

noncomputable def auxiliaryZ (y : ℝ) : ℝ :=
  Real.sqrt (y / Real.log y)

noncomputable def auxiliaryD (y h : ℝ) : ℝ :=
  y * Real.exp h

noncomputable def auxiliaryA (L : ℝ) : ℝ :=
  (L - Real.log L) / 2

noncomputable def auxiliaryS (L h : ℝ) : ℝ :=
  (L + h) / auxiliaryA L

noncomputable def auxiliaryQ (s : ℝ) : ℝ :=
  Real.log (s - 1) / s

noncomputable def boundedAtTop (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in Filter.atTop, |f L| ≤ C

noncomputable def auxiliarySup (L B : ℝ) : ℝ :=
  sSup (auxiliaryF L B '' auxiliaryInterval L)

/-- Claim 34738: the auxiliary-level objective, its normalization, and its domain. -/
def claim_34738 : Prop :=
  ∀ (L ell B y : ℝ),
    Real.exp 2 < L →
    ell = Real.log L →
    0 < B →
    0 < y →
    L = Real.log y →
      (∀ h : ℝ, h ∈ auxiliaryInterval L →
        auxiliaryG L h =
            (2 * L ^ 2 / (L + h)) *
              Real.log ((L + ell + 2 * h) / (L - ell)) ∧
        auxiliaryF L B h =
            auxiliaryG L h - B * Real.exp h * L ^ 2 / (L + h) ^ 2 ∧
        B * Real.exp h * L ^ 2 / (L + h) ^ 2 =
          (B * auxiliaryD y h / (Real.log (auxiliaryD y h)) ^ 2) /
            (y / (Real.log y) ^ 2)) ∧
      (∀ h : ℝ,
        h ∈ auxiliaryInterval L ↔
          auxiliaryZ y ^ 2 < auxiliaryD y h ∧
            auxiliaryD y h < auxiliaryZ y ^ 4)

/-- Claim 34739: bounded optimization and the displayed derivative bounds. -/
def claim_34739 : Prop :=
  ∀ B : ℝ, 0 < B →
    boundedAtTop
      (fun L => auxiliarySup L B - 4 * Real.log (Real.log L)) ∧
    (∀ᶠ L : ℝ in Filter.atTop,
      Real.exp 2 < L ∧
      (∀ h : ℝ, h ∈ auxiliaryInterval L →
        2 < auxiliaryS L h ∧
        auxiliaryS L h < 4 ∧
        auxiliaryG L h =
          (2 * L ^ 2 / auxiliaryA L) * auxiliaryQ (auxiliaryS L h) ∧
        0 < deriv auxiliaryQ (auxiliaryS L h) ∧
        deriv auxiliaryQ (auxiliaryS L h) ≤ (1 / 2 : ℝ)) ∧
      (∀ h : ℝ, h ∈ auxiliaryInterval L →
        0 < deriv (fun x : ℝ => auxiliaryG L x) h ∧
        deriv (fun x : ℝ => auxiliaryG L x) h ≤ (16 : ℝ)) ∧
      (∀ h : ℝ, h ∈ auxiliaryInterval L → h ≤ 0 →
        auxiliaryG L h ≤ auxiliaryG L 0) ∧
      (∀ h : ℝ, h ∈ auxiliaryInterval L → 0 ≤ h →
        (B * Real.exp h * L ^ 2 / (L + h) ^ 2 ≥
            (B / 4) * Real.exp h) ∧
        (auxiliaryF L B h ≤
          auxiliaryG L 0 + 16 * h - (B / 4) * Real.exp h))) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      (∀ h : ℝ, 0 ≤ h →
        16 * h - (B / 4) * Real.exp h ≤ C)) ∧
    (∀ᶠ L : ℝ in Filter.atTop,
      0 ∈ auxiliaryInterval L ∧
      auxiliaryF L B 0 ≤ auxiliarySup L B) ∧
    Filter.Tendsto
      (fun L => auxiliaryG L 0 - 4 * Real.log (Real.log L))
      Filter.atTop (nhds 0)

end MathlibPlus.Open.ResearchFormalizationAuxiliary
