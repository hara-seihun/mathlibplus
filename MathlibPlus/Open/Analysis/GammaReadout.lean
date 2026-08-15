import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

open MeasureTheory
open scoped BigOperators Interval

/-- The fixed shape parameter in the Gamma readout. -/
def gammaShape : ℝ := 5 / 4

/-- The Gamma(shape, 1) density, extended by zero off its stated support. -/
def gammaDensity (t : ℝ) : ℝ :=
  if 0 < t then
    Real.rpow t (gammaShape - 1) * Real.exp (-t) / Real.Gamma gammaShape
  else 0

/-- Expectation against the displayed Gamma density. -/
def gammaExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), f t * gammaDensity t

/-- Complex-valued expectation against the displayed Gamma density. -/
def gammaExpectationComplex (f : ℝ → ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), f t * (gammaDensity t : ℂ)

/-- The explicit Gamma quotient defining `g_q`. -/
def gammaG (q : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma ((gammaShape : ℂ) + z) / Complex.Gamma (gammaShape : ℂ) *
    Complex.cpow (q : ℂ) z

/-- The real moments `N_k(q)` from the packet. -/
def gammaN (q : ℝ) (k : ℕ) : ℝ :=
  gammaExpectation (fun t => (1 - q * t) ^ k)

/-- The complex power moment used in the differentiation statement. -/
def gammaPowerMoment (q : ℝ) (z : ℂ) : ℂ :=
  gammaExpectationComplex (fun t => Complex.cpow ((q * t : ℝ) : ℂ) z)

/-- The real-logarithm moments on the positive carrier `qT > 0`. -/
def gammaLogMoment (q : ℝ) (m : ℕ) : ℂ :=
  gammaExpectationComplex (fun t => (Real.log (q * t) : ℂ) ^ m)

/-- Claim 50124: differentiation at zero gives the real-logarithm moments. -/
def claim50124 : Prop :=
  ∀ q : ℝ, 0 < q →
    ∀ m : ℕ, iteratedDeriv m (gammaG q) 0 = gammaLogMoment q m

/-- Signed Stirling numbers of the first kind. -/
def signedStirlingFirst : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      signedStirlingFirst n k - (n : ℤ) * signedStirlingFirst n (k + 1)

/-- The coefficient `c_{k,m} = m! |s(k,m)| / k!`, over the rationals. -/
def stirlingCoeff (k m : ℕ) : ℚ :=
  (m.factorial : ℚ) * (Int.natAbs (signedStirlingFirst k m) : ℚ) /
    (k.factorial : ℚ)

/-- The formal power-series form of `F_m(w)`. -/
def gammaFSeries (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun k => if m ≤ k then stirlingCoeff k m else 0)

/-- The formal series `-log(1-w)`, whose coefficient at `w^k` is `1/k` for `k > 0`. -/
def negLogOneSubXSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun k => if k = 0 then 0 else 1 / (k : ℚ))

/-- The order-one Borel transform, including its separately specified `E_0`. -/
def gammaE (m : ℕ) (v : ℂ) : ℂ :=
  if m = 0 then 1 else
    ∑' k : ℕ,
      if m ≤ k then
        (stirlingCoeff k m : ℂ) / (k.factorial : ℂ) * v ^ k
      else 0

/-- Claim 50128: the factorial-normalized generating-function identity. -/
def claim50128 : Prop :=
  ∀ m : ℕ, gammaFSeries m = negLogOneSubXSeries ^ m

/-- The real logarithmic kernel in the endpoint-subtracted representation. -/
def gammaL (t : ℝ) : ℝ :=
  Real.log (t / (1 - t))

/-- The removable endpoint value of `(exp (zt) - 1) / t`. -/
def gammaSubtractedExp (z : ℂ) (t : ℝ) : ℂ :=
  if t = 0 then 0 else
    (Complex.exp (z * (t : ℂ)) - 1) / (t : ℂ)

/-- The right-hand side of the analytic representation in claim 50136. -/
def gammaERepresentation (m : ℕ) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (((m - 1) / 2) + 1)) (fun ell =>
    ((m.factorial : ℂ) * (-1 : ℂ) ^ ell * (Real.pi : ℂ) ^ (2 * ell) /
        ((2 * ell + 1).factorial : ℂ) /
        (m - 2 * ell - 1).factorial) *
      (intervalIntegral (fun t : ℝ =>
          gammaSubtractedExp z t * (gammaL t) ^ (m - 2 * ell - 1))
        (0 : ℝ) 1 volume))

/-- Claim 50136: the analytic, complex-`z` continuation formula for `E_m`. -/
def claim50136 : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ z : ℂ, gammaE m z = gammaERepresentation m z

/-- The Taylor series of the Gamma Laplace transform. -/
def gammaNhat (q : ℝ) (u : ℂ) : ℂ :=
  ∑' k : ℕ, (gammaN q k : ℂ) * u ^ k / (k.factorial : ℂ)

/-- The expectation `E exp(u(1-qT))` in the Laplace-transform identity. -/
def gammaLaplaceExpectation (q : ℝ) (u : ℂ) : ℂ :=
  gammaExpectationComplex (fun t =>
    Complex.exp (u * ((1 - q * t : ℝ) : ℂ)))

/-- The closed form of the Gamma Laplace transform. -/
def gammaNhatClosed (q : ℝ) (u : ℂ) : ℂ :=
  Complex.exp u * Complex.cpow (1 + (q : ℂ) * u) (-(gammaShape : ℂ))

/-- The coefficient-level Taylor germ of `Nhat_q`. -/
def gammaNhatSeries (q : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => (gammaN q k : ℂ) / (k.factorial : ℂ))

/-- The coefficient-level series `F_m` over the complex numbers. -/
def gammaFSeriesComplex (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => if m ≤ k then (stirlingCoeff k m : ℂ) else 0)

/-- The filtered readout written with its displayed coefficient normalization. -/
def gammaPhi (m : ℕ) (q : ℝ) (v : ℂ) : ℂ :=
  ∑' k : ℕ,
    if m ≤ k then
      (stirlingCoeff k m : ℂ) * (gammaN q k : ℂ) /
        (k.factorial : ℂ) * v ^ k
    else 0

/-- Coefficientwise product of two formal Taylor germs. -/
def coefficientwiseProduct (A B : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => (PowerSeries.coeff k) A * (PowerSeries.coeff k) B)

/-- The formal Taylor germ of the filtered readout. -/
def gammaPhiSeries (m : ℕ) (q : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k =>
    if m ≤ k then
      (stirlingCoeff k m : ℂ) * (gammaN q k : ℂ) / (k.factorial : ℂ)
    else 0)

/-- Claim 50140: the Gamma Laplace formula and the Hadamard germ identity. -/
def claim50140 : Prop :=
  ∀ q : ℝ, 0 < q →
    ((∀ u : ℂ, 0 < (1 + (q : ℂ) * u).re →
        gammaNhat q u = gammaLaplaceExpectation q u ∧
          gammaLaplaceExpectation q u = gammaNhatClosed q u) ∧
      ∀ m : ℕ,
        gammaPhiSeries m q =
          coefficientwiseProduct (gammaNhatSeries q) (gammaFSeriesComplex m))

end

end MathlibPlus.Open.Analysis
