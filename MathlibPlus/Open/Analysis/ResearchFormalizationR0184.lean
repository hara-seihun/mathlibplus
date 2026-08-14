import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0184

/-- Claim 18609.  The packet's first-cell auxiliary quantity remains an
explicit numerical carrier rather than being replaced by a guessed formula. -/
def claim18609_firstCellTailEstimate (h : ℝ → ℝ → ℝ) : Prop :=
  ∀ q l : ℝ, Real.pi ≤ q → 4 ≤ l → h q l < (l⁻¹) ^ 5

/-- The displayed polynomial on the right side of Claim 18614. -/
def firstResultantFactorOne (q l : ℝ) : ℝ :=
  let y : ℝ := l + l⁻¹
  16 * q ^ 4 * y ^ 4 - 352 * q ^ 3 * y ^ 3 +
      2840 * q ^ 2 * y ^ 2 + 64 * q ^ 2 - 10296 * q * y + 14157

/-- The displayed polynomial on the right side of Claim 18615. -/
def firstResultantFactorTwo (q l : ℝ) : ℝ :=
  let y : ℝ := l + l⁻¹
  16 * q ^ 4 * y ^ 4 - 224 * q ^ 3 * y ^ 3 +
      1112 * q ^ 2 * y ^ 2 + 64 * q ^ 2 - 2520 * q * y + 2205

/-- Claim 18614.  `R1` is kept as the packet's resultant factor and the
quotient identity is stated without defining `R1` by the displayed side. -/
def claim18614_firstResultantFactor (R1 : ℝ → ℝ → ℝ) : Prop :=
  ∀ q l : ℝ, R1 q l / l ^ 4 = firstResultantFactorOne q l

/-- Claim 18615. -/
def claim18615_secondResultantFactor (R2 : ℝ → ℝ → ℝ) : Prop :=
  ∀ q l : ℝ, R2 q l / l ^ 4 = firstResultantFactorTwo q l

/-- Claim 18619.  `G` denotes the one-variable wall function at the
`q = π` endpoint, as in the claim. -/
def claim18619_exactFifthWallDerivative (G : ℝ → ℝ) : Prop :=
  let value : ℝ :=
    2 * (3072 * Real.pi ^ 5 - 34560 * Real.pi ^ 4 +
      164480 * Real.pi ^ 3 - 393120 * Real.pi ^ 2 +
      448140 * Real.pi - 190575)
  iteratedDeriv 5 G 0 = value ∧ value > 0

/-- Claim 18620.  The decimal endpoints are retained as exact rationals. -/
def claim18620_fourthWallDerivativePositive (G : ℝ → ℝ) : Prop :=
  ∀ x : ℝ,
    x ∈ Set.Icc (((10 : ℝ)⁻¹) ^ 6) ((1387 : ℝ) / 1000) →
      iteratedDeriv 4 G x > 0

end MathlibPlus.Open.Analysis.ResearchFormalizationR0184
