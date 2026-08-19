import MathlibPlus.NumberTheory.CompletedZetaRadial

namespace MathlibPlus.Open.NewResearch2.LunaBatch.O0072Repair

noncomputable section

open Complex

noncomputable def xi12810 (s : ℂ) : ℂ :=
  MathlibPlus.NumberTheory.CompletedZetaRadial.riemannXi s

noncomputable def Xi12810 (z : ℂ) : ℂ :=
  xi12810 ((1 / 2 : ℂ) + Complex.I * z)

noncomputable def E12810 (ω : ℝ) (z : ℂ) : ℂ :=
  Xi12810 (z + Complex.I * (ω : ℂ))

noncomputable def Esharp12810 (ω : ℝ) (z : ℂ) : ℂ :=
  Xi12810 (z - Complex.I * (ω : ℂ))

/-- The centered de Branges kernel, with its removable diagonal value given
by the analytic continuation of the displayed quotient. -/
noncomputable def deBrangesKernel12810 (ω : ℝ) (w z : ℂ) : ℂ :=
  if z = starRingEnd ℂ w then
    -deriv
        (fun q : ℂ => E12810 ω q * starRingEnd ℂ (E12810 ω w) -
          Esharp12810 ω q * starRingEnd ℂ (Esharp12810 ω w))
        (starRingEnd ℂ w) /
      (2 * (Real.pi : ℂ) * Complex.I)
  else
    (E12810 ω z * starRingEnd ℂ (E12810 ω w) -
      Esharp12810 ω z * starRingEnd ℂ (Esharp12810 ω w)) /
      (2 * (Real.pi : ℂ) * Complex.I *
        (starRingEnd ℂ w - z))

noncomputable def diagonalKernel12810 (ω : ℝ) (z : ℂ) : ℝ :=
  (deBrangesKernel12810 ω z z).re

def diagonalDerivativeNonnegative12810 : Prop :=
  ∀ z : ℂ, 0 < z.im →
    ∀ ω : ℝ, 0 < ω → ω < 1 / 2 →
      0 ≤ deriv (fun u : ℝ => diagonalKernel12810 u z) ω

def integratedDiagonalNonnegative12810 : Prop :=
  ∀ z : ℂ, 0 < z.im →
    ∀ ω : ℝ, 0 < ω → ω < 1 / 2 →
      diagonalKernel12810 0 z = 0 ∧ 0 ≤ diagonalKernel12810 ω z

def diagonalZeroIdentity12810 (ζ : ℂ) : Prop :=
  ∀ ω : ℝ, 0 < ω → ω < ζ.im →
    diagonalKernel12810 ω (ζ - (ω : ℂ) * Complex.I) =
      -Complex.normSq
          (Xi12810 (ζ - 2 * (ω : ℂ) * Complex.I)) /
        (4 * Real.pi * (ζ.im - ω))

def verticalZeroSet12810 (ζ : ℂ) : Prop :=
  ∀ ω : ℝ, 0 < ω → ω < ζ.im →
    Xi12810 (ζ - 2 * (ω : ℂ) * Complex.I) = 0

def identityTheoremExcludesVerticalZeros12810 : Prop :=
  ∀ ζ : ℂ, Xi12810 ζ = 0 → 0 < ζ.im → ζ.im < 1 / 2 →
    ¬ verticalZeroSet12810 ζ

def rh12810 : Prop :=
  ∀ ρ : ℂ, xi12810 ρ = 0 → ρ.re = 1 / 2

/-- Claim 12810: the exact diagonal derivative range integrates from the
zero kernel, and an off-critical zero would propagate to a forbidden vertical
continuum; the identity theorem therefore yields the full RH predicate. -/
def claim12810 : Prop :=
  diagonalDerivativeNonnegative12810 →
    (∀ w z : ℂ, deBrangesKernel12810 0 w z = 0) ∧
    integratedDiagonalNonnegative12810 ∧
    (∀ ζ : ℂ, Xi12810 ζ = 0 → 0 < ζ.im → ζ.im < 1 / 2 →
      diagonalZeroIdentity12810 ζ ∧
        (∀ ω : ℝ, 0 < ω → ω < ζ.im →
          0 ≤ diagonalKernel12810 ω (ζ - (ω : ℂ) * Complex.I) →
          Xi12810 (ζ - 2 * (ω : ℂ) * Complex.I) = 0) ∧
        identityTheoremExcludesVerticalZeros12810) ∧
    rh12810

end

end MathlibPlus.Open.NewResearch2.LunaBatch.O0072Repair
