import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.FormalizationBatchExponential

/-- The measure `dt / t^2` on the half-line `[1, ∞)`. -/
noncomputable def nymanHMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.withDensity
    (MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.Ici (1 : ℝ)))
    (fun t => ENNReal.ofReal (1 / t ^ 2))

/-- The stated Hilbert carrier `H = L²([1,∞), dt/t²)`. -/
noncomputable abbrev NymanH := MeasureTheory.Lp ℝ 2 nymanHMeasure

/-- The Möbius coefficient used by the damped Nyman sums. -/
def nymanMobiusInt (n : ℕ) : ℤ := ArithmeticFunction.moebius n

def nymanMobiusReal (n : ℕ) : ℝ := (nymanMobiusInt n : ℝ)

def nymanMobiusComplex (n : ℕ) : ℂ := (nymanMobiusInt n : ℂ)

/-- `γ_n(t) = ⌊t/n⌋ - ⌊t⌋/n`, with the displayed sum convention at `n = 0`. -/
noncomputable def nymanGenerator (n : ℕ) (t : ℝ) : ℝ :=
  if 0 < n then
    (Int.floor (t / (n : ℝ)) : ℝ) - (Int.floor t : ℝ) / (n : ℝ)
  else 0

/-- The exponentially damped Nyman function in Claim 13759. -/
noncomputable def expDampedNymanFunction (u t : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      nymanMobiusReal n * Real.exp (-((n : ℝ) * u)) * nymanGenerator n t
    else 0

/-- The interval error coefficient `h_k(u)` in Claim 13759. -/
noncomputable def expDampedErrorCoefficient (u : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      nymanMobiusReal n * (k % n : ℝ) * Real.exp (-((n : ℝ) * u)) / (n : ℝ)
    else 0

/-- The square of the `H` norm, via the `L²` norm for `nymanHMeasure`. -/
noncomputable def nymanHNormSquared (g : ℝ → ℝ) : ℝ :=
  (MeasureTheory.eLpNorm g 2 nymanHMeasure).toReal ^ 2

/--
Exact unit-interval formula for the exponentially damped Nyman function, including
its positive-damping hypothesis and the `L²([1,∞),dt/t²)` error formula.
-/
def claim13759_exactUnitIntervalErrorFormula : Prop :=
  ∀ u : ℝ, 0 < u →
    (∀ k : ℕ, 0 < k →
      ∀ t : ℝ, (k : ℝ) ≤ t → t < (k + 1 : ℝ) →
        expDampedNymanFunction u t = -expDampedErrorCoefficient u k) ∧
    nymanHNormSquared (fun t => expDampedNymanFunction u t - 1) =
      ∑' k : ℕ,
        if 0 < k then
          ‖expDampedErrorCoefficient u k + 1‖ ^ 2 /
            ((k : ℝ) * (k + 1 : ℝ))
        else 0

/-- `R_j(x) = Σ_{n|j} μ(n)x^n`. -/
noncomputable def lambertCoefficient (j : ℕ) (x : ℝ) : ℝ :=
  (Nat.divisors j).sum (fun n => nymanMobiusReal n * x ^ n)

/-- The first Lambert series defining `L_x(z)`. -/
noncomputable def lambertL (x : ℝ) (z : ℂ) : ℂ :=
  ∑' j : ℕ,
    if 0 < j then (lambertCoefficient j x : ℂ) * z ^ j else 0

/-- The divisor-indexed Lambert series equal to `L_x(z)`. -/
noncomputable def lambertDivisorSeries (x : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ,
    if 0 < n then
      nymanMobiusComplex n * (x : ℂ) ^ n * z ^ n / (1 - z ^ n)
    else 0

/-- `g(x) = Σ μ(n)x^n/n`. -/
noncomputable def lambertG (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then nymanMobiusReal n * x ^ n / (n : ℝ) else 0

/-- The common convergence domain used by the Lambert identity. -/
def lambertCommonDomain (u : ℝ) (z : ℂ) : Prop :=
  (Summable (fun k : ℕ =>
    if 0 < k then
      (expDampedNymanFunction u (k : ℝ) - 1 : ℝ) * z ^ k
    else 0)) ∧
  (Summable (fun j : ℕ =>
    if 0 < j then (lambertCoefficient j (Real.exp (-u)) : ℂ) * z ^ j
    else 0)) ∧
  (Summable (fun n : ℕ =>
    if 0 < n then
      nymanMobiusComplex n * (Real.exp (-u) : ℂ) ^ n * z ^ n / (1 - z ^ n)
    else 0)) ∧
  (Summable (fun n : ℕ =>
    if 0 < n then
      nymanMobiusReal n * Real.exp (-u) ^ n / (n : ℝ)
    else 0)) ∧
  z ≠ 1 ∧
  ∀ n : ℕ, 0 < n → z ^ n ≠ 1

/--
Lambert-series generating identity from Claim 13760, on the common domain of
convergence and with `x = exp(-u)`. The error coefficient is the exact
`f_u(k)-1` from Claim 13759.
-/
def claim13760_lambertSeriesGeneratingIdentity : Prop :=
  ∀ u : ℝ, 0 < u →
    let x := Real.exp (-u)
    ∀ z : ℂ, lambertCommonDomain u z →
      lambertL x z = lambertDivisorSeries x z ∧
        (∑' k : ℕ,
          if 0 < k then
            (expDampedNymanFunction u (k : ℝ) - 1 : ℂ) * z ^ k
          else 0) =
          lambertL x z / (1 - z) -
            (lambertG x : ℂ) * z / (1 - z) ^ 2 - z / (1 - z)

end MathlibPlus.Open.Analysis.FormalizationBatchExponential
