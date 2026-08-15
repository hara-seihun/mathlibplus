import Mathlib

noncomputable section

open scoped BigOperators
open Set MeasureTheory Filter Topology
open Classical

namespace MathlibPlus.Open.Analysis.ZetaHardy

/-- A finitely supported complex coefficient sequence, with the zero index unused. -/
def finiteComplexCoefficients (c : ℕ → ℂ) : Prop :=
  Set.Finite (Function.support c)

/-- The finite pole-cancelling multiplier written as an unconditional series. -/
def finiteDirichletMultiplier (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' d : ℕ,
    if 0 < d then c d * (d : ℂ) ^ (-s) else 0

/-- The pole-cancellation condition. -/
def poleCancellationCondition (c : ℕ → ℂ) : Prop :=
  (∑' d : ℕ,
    if 0 < d then c d / (d : ℂ) else 0) = 0

/-- The center value supplied by a simple zero of the multiplier. -/
def finitePoleCancelledCenterValue (c : ℕ → ℂ) : ℂ :=
  -∑' d : ℕ,
    if 0 < d then c d * (Real.log d : ℂ) / (d : ℂ) else 0

/-- The pole-cancelled family, with the center value made explicit. -/
def finitePoleCancelledFamily (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then finitePoleCancelledCenterValue c
  else finiteDirichletMultiplier c s * riemannZeta s

/-- Claim 9371: geometric pole-cancelling zeta family. -/
def geometricPoleCancellingZetaFamilyClaim : Prop :=
  ∀ q : ℕ,
    2 ≤ q →
    (1 - (q : ℂ) ^ ((1 : ℂ) - 1)) = 0 ∧
      AnalyticAt ℂ
        (fun s : ℂ =>
          if s = 1 then (Real.log q : ℂ)
          else (1 - (q : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) 1

/-- Claim 9372: removable center value. -/
def removableCenterValueClaim : Prop :=
  ∀ q : ℕ,
    2 ≤ q →
    AnalyticAt ℂ
        (fun s : ℂ =>
          if s = 1 then (Real.log q : ℂ)
          else (1 - (q : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) 1 ∧
      (if (1 : ℂ) = 1 then (Real.log q : ℂ)
       else (1 - (q : ℂ) ^ ((1 : ℂ) - 1)) * riemannZeta 1) =
        (Real.log q : ℂ)

/-- The critical Cauchy Hardy norm in Claim 9376. -/
def criticalCauchyHardyNorm (q : ℕ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ t : ℝ,
      ‖(if ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 1 then
          (Real.log q : ℂ)
        else
          (1 - (q : ℂ) ^ ((1 : ℂ) - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) *
            riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2 /
        (1 / 4 + t ^ 2)

/-- Claim 9376: exact critical Cauchy Hardy norm. -/
def exactCriticalCauchyHardyNormClaim : Prop :=
  ∀ q : ℕ,
    2 ≤ q →
    criticalCauchyHardyNorm q =
      ∑' n : ℕ,
        if 0 < n then
          (((n % q : ℕ) : ℝ) ^ 2) /
            ((n : ℝ) * (n + 1))
        else 0

/-- The real-valued digamma function used in the residue grouping formula. -/
def realDigamma (x : ℝ) : ℝ :=
  (Complex.digamma (x : ℂ)).re

/-- Claim 9377: exact digamma form and the q=2 value. -/
def exactDigammaFormAndTwoValueClaim : Prop :=
  ∀ q : ℕ,
    2 ≤ q →
    criticalCauchyHardyNorm q =
        (1 / (q : ℝ)) *
          ∑ r ∈ Finset.Icc 1 (q - 1),
            (r : ℝ) ^ 2 *
              (realDigamma ((r + 1 : ℕ) / (q : ℝ)) -
                realDigamma ((r : ℕ) / (q : ℝ))) ∧
      criticalCauchyHardyNorm 2 =
        (∑' n : ℕ,
          if 0 < n ∧ Odd n then
            1 / ((n : ℝ) * (n + 1))
          else 0) ∧
      criticalCauchyHardyNorm 2 = Real.log 2

/-- The limiting integral constant and its finite partial sums. -/
def asymptoticIntegralConstant : ℝ :=
  ∑' k : ℕ,
    ∫ u in Ioc 0 1, u ^ 2 / ((k : ℝ) + u) ^ 2

def asymptoticIntegralPartialSum (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1),
    ∫ u in Ioc 0 1, u ^ 2 / ((k : ℝ) + u) ^ 2

/-- Claim 9381: asymptotic norm constant and its finite partial sums. -/
def asymptoticNormConstantClaim : Prop :=
  Tendsto
      (fun q : ℕ => criticalCauchyHardyNorm q / (q : ℝ))
      atTop (𝓝 asymptoticIntegralConstant) ∧
    asymptoticIntegralConstant =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant ∧
    1 < Real.log (2 * Real.pi) - Real.eulerMascheroniConstant ∧
    ∀ K : ℕ,
      asymptoticIntegralPartialSum K =
        2 + 2 * (K : ℝ) - (harmonic (K + 1) : ℝ) -
          2 * (K : ℝ) * Real.log (K + 1) +
          2 * Real.log (Nat.factorial K)

/-- Claim 9384: finite pole-cancelling multiplier and removable pole. -/
def finitePoleCancellingMultiplierClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    (poleCancellationCondition c ↔ finiteDirichletMultiplier c 1 = 0) ∧
      (poleCancellationCondition c →
        ∃ F : ℂ → ℂ,
          AnalyticAt ℂ F 1 ∧
            ∀ s, s ≠ 1 →
              F s = finiteDirichletMultiplier c s * riemannZeta s)

/-- Claim 9385: pole-cancelled center value under a simple zero. -/
def poleCancelledCenterValueClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
    (∃ a : ℂ, HasDerivAt (finiteDirichletMultiplier c) a 1 ∧ a ≠ 0) →
    ∃ F : ℂ → ℂ, ∃ a : ℂ,
      AnalyticAt ℂ F 1 ∧
        HasDerivAt (finiteDirichletMultiplier c) a 1 ∧ a ≠ 0 ∧
        (∀ s, s ≠ 1 →
          F s = finiteDirichletMultiplier c s * riemannZeta s) ∧
        F 1 = a ∧
        a = finitePoleCancelledCenterValue c ∧
        finitePoleCancelledCenterValue c =
          -(∑' d : ℕ,
            if 0 < d then c d * (Real.log d : ℂ) / (d : ℂ) else 0) ∧
        finitePoleCancelledCenterValue c ≠ 0

/-- The divisor-convolution coefficients. -/
def divisorConvolutionCoefficient (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, c d

/-- Claim 9386: divisor-convolution Dirichlet coefficients. -/
def divisorConvolutionCoefficientsClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    ∀ s : ℂ,
      1 < s.re →
      finitePoleCancelledFamily c s =
        ∑' n : ℕ,
          if 0 < n then
            divisorConvolutionCoefficient c n * (n : ℂ) ^ (-s)
          else 0

/-- The floor and fractional-part forms of the partial sums. -/
def divisorPartialSum (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 (Nat.floor x)), divisorConvolutionCoefficient c n

def divisorFloorSum (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' d : ℕ,
    if 0 < d then c d * (Nat.floor (x / (d : ℝ)) : ℂ) else 0

def divisorFractionalPartSum (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' d : ℕ,
    if 0 < d then c d * ((Int.fract (x / (d : ℝ)) : ℝ) : ℂ) else 0

/-- Claim 9387: exact floor partial sums, boundedness, and convergence for Re(s)>0. -/
def exactFloorPartialSumsAndBoundednessClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖divisorPartialSum c x‖ ≤ C) ∧
      ∀ x : ℝ, 1 ≤ x →
        divisorPartialSum c x = divisorFloorSum c x ∧
          divisorPartialSum c x = -divisorFractionalPartSum c x ∧
          ∀ s : ℂ, 0 < s.re →
            Summable (fun n : ℕ =>
              if 0 < n then
                divisorConvolutionCoefficient c n * (n : ℂ) ^ (-s)
              else 0)

/-- The max-kernel Hardy energy. -/
def exactMaxKernelHardyEnergy (c : ℕ → ℂ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ t : ℝ,
      ‖finitePoleCancelledFamily c ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 /
        (1 / 4 + t ^ 2)

/-- Claim 9388: exact max-kernel Hardy energy. -/
def exactMaxKernelHardyEnergyClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖divisorPartialSum c x‖ ≤ C) →
    exactMaxKernelHardyEnergy c =
        (∑' n : ℕ,
          if 0 < n then
            ‖divisorPartialSum c n‖ ^ 2 /
              ((n : ℝ) * (n + 1))
          else 0) ∧
      exactMaxKernelHardyEnergy c =
        ∫ y in Ici 1, ‖divisorPartialSum c y‖ ^ 2 / y ^ 2

/-- The literal Nyman coordinate. -/
def literalNymanCoordinate (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' d : ℕ,
    if 0 < d then c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ) else 0

/-- Claim 9389: literal Nyman coordinate and its reciprocal relation. -/
def literalNymanCoordinateClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    ∀ x : ℝ, 0 < x → x < 1 →
      literalNymanCoordinate c x =
        (∑' d : ℕ,
          if 0 < d then c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ) else 0) ∧
      ∀ y : ℝ, 1 < y →
        literalNymanCoordinate c (1 / y) = -divisorPartialSum c y

/-- The Nyman and Hardy square norms. -/
def nymanEnergy (c : ℕ → ℂ) : ℝ :=
  ∫ x in Ioc 0 1, ‖literalNymanCoordinate c x‖ ^ 2

def hardyNorm (c : ℕ → ℂ) : ℝ :=
  Real.sqrt (exactMaxKernelHardyEnergy c)

def nymanNorm (c : ℕ → ℂ) : ℝ :=
  Real.sqrt (nymanEnergy c)

/-- Claim 9390: exact Hardy/Nyman isometry. -/
def exactHardyNymanIsometryClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖divisorPartialSum c x‖ ≤ C) →
    hardyNorm c = nymanNorm c

/-- The center series and center integral. -/
def centerPartialSumSeries (c : ℕ → ℂ) : ℂ :=
  ∑' n : ℕ,
    if 0 < n then
      divisorPartialSum c n / ((n : ℂ) * (n + 1))
    else 0

def centerPartialSumIntegral (c : ℕ → ℂ) : ℂ :=
  ∫ y in Ici 1, divisorPartialSum c y / (y : ℂ) ^ 2

def nymanCenterIntegral (c : ℕ → ℂ) : ℂ :=
  ∫ x in Ioc 0 1, literalNymanCoordinate c x

/-- Claim 9391: center integral identity. -/
def centerIntegralIdentityClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
    finitePoleCancelledFamily c 1 = centerPartialSumSeries c ∧
      finitePoleCancelledFamily c 1 = centerPartialSumIntegral c ∧
      nymanCenterIntegral c = -finitePoleCancelledFamily c 1

/-- The normalized Nyman approximation error. -/
def normalizedNymanEvaluationError (c : ℕ → ℂ) : ℝ :=
  ∫ x in Ioc 0 1,
    ‖(1 : ℂ) + literalNymanCoordinate c x /
      finitePoleCancelledFamily c 1‖ ^ 2

/-- Claim 9392: normalized evaluation-gap identity. -/
def normalizedEvaluationGapIdentityClaim : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
    finitePoleCancelledFamily c 1 ≠ 0 →
    normalizedNymanEvaluationError c =
      exactMaxKernelHardyEnergy c /
          ‖finitePoleCancelledFamily c 1‖ ^ 2 - 1

end MathlibPlus.Open.Analysis.ZetaHardy
