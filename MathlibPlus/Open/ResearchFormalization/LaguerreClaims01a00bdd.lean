import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.LaguerreClaims01a00bdd

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The parameter-two generalized Laguerre polynomial used by the integrated
Laguerre discrepancy map. -/
def laguerreTwo14368 (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ k * (Nat.choose (m + 2) (m - k) : ℝ) * t ^ k /
      (Nat.factorial k : ℝ)

/-- The integrated Laguerre coefficients, with the first two coefficients zero. -/
noncomputable def integratedLaguerreCoefficients14368
    (B : ℝ → ℝ) (n : ℕ) : ℝ :=
  if n < 2 then 0 else
    ∫ t in Set.Ioi (0 : ℝ), laguerreTwo14368 (n - 2) t * B t

/-- The ordinary Poisson--Fock square norm of a real coefficient sequence. -/
noncomputable def poissonFockSqNorm14368 (x : ℝ) (u : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ,
    Real.exp (-x) * x ^ n * |u n| ^ 2 /
      (Nat.factorial n : ℝ)

/-- The ordinary Poisson--Fock norm. -/
noncomputable def poissonFockNorm14368 (x : ℝ) (u : ℕ → ℝ) : ℝ :=
  Real.sqrt (poissonFockSqNorm14368 x u)

/-- The stretched-exponential tangent exponent. -/
def tangentQ14368 (α : ℝ) : ℝ :=
  α / (1 - α)

/-- The tangent constant `C_{α,c}`. -/
def tangentConstant14368 (α c : ℝ) : ℝ :=
  c * (1 - α) * Real.rpow (c * α) (tangentQ14368 α)

/-- The tangent amplitude `a_δ = exp(-C_{α,c} δ^{-q})`. -/
def tangentAmplitude14368 (α c δ : ℝ) : ℝ :=
  Real.exp (-tangentConstant14368 α c * Real.rpow δ (-(tangentQ14368 α)))

/-- The exact Laguerre transform pole ratio `r_δ`. -/
def poleRatio14368 (δ : ℝ) : ℝ :=
  -(1 - δ) / δ

/-- The geometric mode supported on the indices `n ≥ 2`. -/
def geometricMode14368 (α c δ : ℝ) : ℕ → ℝ := fun n =>
  if 2 ≤ n then
    tangentAmplitude14368 α c δ * δ * (poleRatio14368 δ) ^ n
  else 0

/-- Claim 14368: the exact geometric-mode Poisson--Fock square norm, with the
parameter ranges and the named tangent amplitude inherited from the admitted
Poisson--Fock and tangent statements. -/
def exactGeometricModeFockNorm14368 : Prop :=
  ∀ (α c δ x : ℝ),
    0 < α → α < 1 → 0 < c → 0 < δ → 0 < x →
      (poissonFockNorm14368 x (geometricMode14368 α c δ)) ^ 2 =
        (tangentAmplitude14368 α c δ) ^ 2 * δ ^ 2 * Real.exp (-x) *
          (Real.exp (x * (poleRatio14368 δ) ^ 2) - 1 -
            x * (poleRatio14368 δ) ^ 2)

/-- The amplitude-weighted tangent exponential after deleting its prefix on
`[0,T)`.  No sign restriction on `T` is imposed. -/
def tangentTail14371 (α c δ T t : ℝ) : ℝ :=
  if T ≤ t then
    tangentAmplitude14368 α c δ * Real.exp (-δ * t)
  else 0

/-- Claim 14371: the tangent-tail lower bound has an error constant depending
only on `x` and `T`, and the resulting norm diverges in the sub-two-thirds
regime. -/
def lowerBoundAsymptotic14371 : Prop :=
  ∀ (x T : ℝ), 0 < x →
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (α c : ℝ), 0 < α → α < 1 → 0 < c →
        ∃ δ₀ : ℝ, 0 < δ₀ ∧
          (∀ δ : ℝ, 0 < δ → δ < δ₀ →
            x / (2 * δ ^ 2) -
                tangentConstant14368 α c *
                  Real.rpow δ (-(tangentQ14368 α)) -
                K * (δ⁻¹ + |Real.log δ|) ≤
              Real.log
                (poissonFockNorm14368 x
                  (integratedLaguerreCoefficients14368
                    (tangentTail14371 α c δ T)))) ∧
          (tangentQ14368 α < 2 ↔ α < (2 / 3 : ℝ)) ∧
          (tangentQ14368 α < 2 →
            Filter.Tendsto
              (fun δ : ℝ =>
                Real.log
                  (poissonFockNorm14368 x
                    (integratedLaguerreCoefficients14368
                      (tangentTail14371 α c δ T))))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop)

end

end MathlibPlus.Open.ResearchFormalization.LaguerreClaims01a00bdd
