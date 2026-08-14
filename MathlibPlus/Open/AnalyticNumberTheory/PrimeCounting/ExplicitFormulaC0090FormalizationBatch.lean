import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 1356: the exact explicit-formula specialization parameters and
all displayed derived quantities. -/
def exactSpecializationParameters_claim1356 : Prop :=
  let α : ℝ := (817 : ℝ) / 50000
  let omega : ℝ := (397 : ℝ) / 500
  let D : ℝ := (51 : ℝ) / 100
  let lambda : ℝ := (1177 : ℝ) / 20000
  let thetaPrime : ℝ := (8029 : ℝ) / 10000
  (α = (817 : ℝ) / 50000 ∧
    omega = (397 : ℝ) / 500 ∧
    D = (51 : ℝ) / 100 ∧
    lambda = (1177 : ℝ) / 20000 ∧
    thetaPrime = (8029 : ℝ) / 10000) ∧
    (∀ x u : ℝ, 0 < x →
      let L := Real.log x
      let h := 64 * Real.rpow x ((63 : ℝ) / 64)
      let s := h / x
      let X := x + h
      let Z := Real.log X
      let T := Real.exp u / 2
      let U := Real.exp u
      h = 64 * Real.rpow x ((63 : ℝ) / 64) ∧
        s = 64 * Real.exp (-L / 64) ∧
        X = x + h ∧ Z = Real.log X ∧
        T = Real.exp u / 2 ∧ U = Real.exp u)

/-- Claim 1357: the four-branch Appendix-A zero-free contour width. -/
def fourBranchAppendixAZeroFreeWidth_claim1357 : Prop :=
  let α : ℝ := (817 : ℝ) / 50000
  ∀ z : ℝ, 0 < z →
    let y := α * z
    let J := y / 6 + Real.log y + Real.log (618 : ℝ) / 1000
    let R_F :=
      (J + (685 : ℝ) / 1000 + (155 : ℝ) / 100 * Real.log y) /
        (y * ((4962 : ℝ) / 100000 - (196 : ℝ) / 10000 / (J + (115 : ℝ) / 100)))
    let branch₁ := 1 / ((5558691 : ℝ) / 1000000 * y)
    let branch₂ := 1 / (R_F * y)
    let branch₃ := Real.log y / ((21233 : ℝ) / 1000 * y)
    let branch₄ := 1 / ((53989 : ℝ) / 1000 *
      Real.rpow y ((2 : ℝ) / 3) * Real.rpow (Real.log y) ((1 : ℝ) / 3))
    ∃ ν : ℝ,
      branch₁ ≤ ν ∧ branch₂ ≤ ν ∧ branch₃ ≤ ν ∧ branch₄ ≤ ν ∧
      (ν = branch₁ ∨ ν = branch₂ ∨ ν = branch₃ ∨ ν = branch₄)

/-- Claim 1364: the shared source-window conditions and their logarithmic
forms after the displayed substitution `T = exp u / 2`. -/
def sharedSourceWindowConditions_claim1364 : Prop :=
  let α : ℝ := (817 : ℝ) / 50000
  let lambda : ℝ := (1177 : ℝ) / 20000
  let thetaPrime : ℝ := (8029 : ℝ) / 10000
  ∀ x u : ℝ, 0 < x →
    let L := Real.log x
    let h := 64 * Real.rpow x ((63 : ℝ) / 64)
    let X := x + h
    let Z := Real.log X
    let T := Real.exp u / 2
    let window :=
      max (51 : ℝ) (Z ^ 2) < T ∧ T > Z ^ 2 ∧
        T < (Real.rpow x α - 2) / 4 ∧ thetaPrime / T ≤ lambda
    window →
      u - Real.log 2 > 2 * Real.log Z ∧
        α * L > u + Real.log 2 + Real.log (1 + Real.exp (-u))

/-- Claim 1371: positivity of the exponent-64 short theta increment on the
large-x range. -/
def largeXPositiveThetaDifference_claim1371 : Prop :=
  ∀ x : ℝ, Real.exp 1946 ≤ x →
    0 < Chebyshev.theta (x + 64 * Real.rpow x ((63 : ℝ) / 64)) -
      Chebyshev.theta x

/-- Claim 1373: the low-range splice for the exponent-64 theta increment and
the exact displayed logarithmic seam. -/
def lowRangeThetaDifferenceSplice_claim1373 : Prop :=
  let L₀ : ℝ :=
    64 * Real.log ((64 : ℝ) * 251949000000 *
      (1 - 1 / (251949000000 : ℝ)) ^ 2)
  ((1946328038808025526 : ℝ) / 10 ^ 15 < L₀ ∧
    L₀ < (1946328038808025527 : ℝ) / 10 ^ 15 ∧
    1946 < L₀) ∧
    (∀ x : ℝ, 4 * 10 ^ 18 ≤ x → x ≤ Real.exp L₀ →
      0 < Chebyshev.theta (x + 64 * Real.rpow x ((63 : ℝ) / 64)) -
        Chebyshev.theta x)

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
