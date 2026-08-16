import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.ExponentialMellinBergman

noncomputable section

/-- The measure `dt/t²` on `[1,∞)`. -/
def hMeasure : MeasureTheory.Measure ℝ :=
  (MeasureTheory.MeasureSpace.volume.restrict (Set.Ici (1 : ℝ))).withDensity
    (fun t : ℝ => ENNReal.ofReal (1 / t ^ 2))

/-- The stated Hilbert carrier `L²([1,∞), dt/t²)`. -/
def H : Type := MeasureTheory.Lp ℝ 2 hMeasure

/-- Squared norm in the displayed weighted `L²` carrier. -/
def hNormSq (f : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ, f t ^ 2 ∂hMeasure

/-- The Nyman generator appearing in the exponentially damped profile. -/
def gamma (n : ℕ) (t : ℝ) : ℝ :=
  (Int.floor (t / (n : ℝ)) : ℝ) - (Int.floor t : ℝ) / (n : ℝ)

noncomputable def moebiusReal (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ)

noncomputable def moebiusComplex (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ)

/-- The exponentially damped Nyman profile `f_u`. -/
noncomputable def dampedProfile (u t : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      moebiusReal n * Real.exp (-((n : ℝ) * u)) * gamma n t
    else 0

/-- `E_k(x)=f_u(k)-1` at `x=e⁻ᵘ`, with the zero coefficient omitted. -/
noncomputable def bergmanErrorCoefficient (x : ℝ) (k : ℕ) : ℂ :=
  if 0 < x ∧ 0 < k then
    Complex.ofReal (dampedProfile (-Real.log x) (k : ℝ) - 1)
  else 0

noncomputable def bergmanErrorSeries (x : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ,
    if 0 < k then bergmanErrorCoefficient x k * z ^ k else 0

/-- Weighted Bergman error identity for the exponentially damped profile. -/
def weightedBergmanErrorIdentity : Prop :=
  ∀ u : ℝ, 0 < u →
    hNormSq (fun t => dampedProfile u t - 1) =
      (1 / Real.pi) *
        ∫ z : ℂ in Metric.ball (0 : ℂ) 1,
          ‖bergmanErrorSeries (Real.exp (-u)) z‖ ^ 2 *
            (1 - ‖z‖ ^ 2) / ‖z‖ ^ 2
          ∂MeasureTheory.MeasureSpace.volume

/-- The exponentially damped Möbius Dirichlet series `A_u(s)`. -/
noncomputable def dampedMellin (u : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ,
    if 0 < n then
      moebiusComplex n * Complex.exp (-((n : ℂ) * (u : ℂ))) *
          Complex.cpow (n : ℂ) (-s)
    else 0

/-- The scalar `g_u` in the Mellin energy identity. -/
noncomputable def dampedMellinScalar (u : ℝ) : ℂ :=
  ∑' n : ℕ,
    if 0 < n then
      moebiusComplex n * Complex.exp (-((n : ℂ) * (u : ℂ))) / (n : ℂ)
    else 0

/-- The vertical-line parameterization of the contour integral on `Re w = c`. -/
noncomputable def inverseMellinContour (u : ℝ) (s : ℂ) (c : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    ∫ t : ℝ,
      (Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ)) *
          Complex.cpow (u : ℂ) (-((c : ℂ) + Complex.I * (t : ℂ))) /
          riemannZeta (s + (c : ℂ) + Complex.I * (t : ℂ))) * Complex.I
      ∂MeasureTheory.MeasureSpace.volume

/-- Exact exponential Mellin energy together with the inverse Mellin formula
in the initial half-plane. -/
def exponentialMellinEnergyAndInverse : Prop :=
  (∀ u : ℝ, 0 < u →
    hNormSq (fun t => dampedProfile u t - 1) =
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
              (dampedMellin u ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) -
                dampedMellinScalar u) - 1‖ ^ 2 /
              ((1 / 4 : ℝ) + t ^ 2))
  ∧
  (∀ u : ℝ, 0 < u → ∀ s : ℂ, ∀ c : ℝ,
    0 < c → 1 < s.re + c →
      dampedMellin u s = inverseMellinContour u s c)

end
end MathlibPlus.Open.Research.ExponentialMellinBergman
