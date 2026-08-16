import MathlibPlus.Open.Analysis.LargeBaseFiberFloor

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.BatchO0313Claim15308

noncomputable section

private def commensurateLog15308 (q : ℤ) : ℝ :=
  Real.log (q : ℝ)

private def commensurateRadius15308 (q : ℤ) : ℝ :=
  Real.rpow (q : ℝ) (-(1 / 2 : ℝ))

private def linearFactorProduct15308 {Index : Type*} [Fintype Index]
    (roots : Index → ℂ) : Polynomial ℂ :=
  ∏ index, (Polynomial.X - Polynomial.C (roots index))

private def circleReflectedFactor15308 (r : ℝ) (root : ℂ) : Polynomial ℂ :=
  Polynomial.C (r : ℂ) *
    (1 - Polynomial.C (star root / (r : ℂ) ^ 2) * Polynomial.X)

private def originalCommensuratePolynomial15308
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient
    * (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2))
    * Polynomial.X ^ zeroMultiplicity
    * linearFactorProduct15308 interiorRoots
    * linearFactorProduct15308 exteriorRoots

private def reflectedCommensuratePolynomial15308
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient
    * (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2))
    * Polynomial.C ((r : ℂ) ^ zeroMultiplicity)
    * (∏ index, circleReflectedFactor15308 r (interiorRoots index))
    * linearFactorProduct15308 exteriorRoots

private def commensuratePoint15308 (q : ℤ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (commensurateLog15308 q : ℂ))

private def criticalCauchyValue15308 (q : ℤ) (P : Polynomial ℂ)
    (t : ℝ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  Polynomial.eval (commensuratePoint15308 q s) P * riemannZeta s

private def criticalCauchyNorm15308 (q : ℤ) (P : Polynomial ℂ) : ℝ :=
  Real.sqrt
    (∫ t : ℝ, ‖criticalCauchyValue15308 q P t‖ ^ 2
      ∂MathlibPlus.Open.Analysis.criticalCauchyMeasure)

private def poleCancelledCenterValue15308 (q : ℤ) (P : Polynomial ℂ) : ℂ :=
  -(commensurateLog15308 q : ℂ) *
    (commensurateRadius15308 q : ℂ) ^ 2 *
    Polynomial.eval ((commensurateRadius15308 q : ℂ) ^ 2) P.derivative

private def completeRemovedNumeratorInnerMass15308
    {Interior : Type*} [Fintype Interior]
    (q : ℤ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ) : ℝ :=
  (zeroMultiplicity : ℝ) * commensurateLog15308 q / 2 +
    ∑ index,
      Real.log
        (commensurateRadius15308 q * ‖1 - interiorRoots index‖ /
          ‖(commensurateRadius15308 q : ℂ) ^ 2 - interiorRoots index‖)

/-- The reflected polynomial normal form, including pointwise boundary
modulus, critical-Cauchy norm, and regularized center-gain conclusions. -/
def claim15308 : Prop :=
  ∀ (q : ℤ) (Interior Exterior : Type*)
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ),
    (2 : ℤ) ≤ q →
    coefficient ≠ 0 →
    (∀ index,
      interiorRoots index ≠ 0 ∧
        ‖interiorRoots index‖ < commensurateRadius15308 q ∧
        interiorRoots index ≠
          (commensurateRadius15308 q : ℂ) ^ 2) →
    (∀ index, commensurateRadius15308 q ≤ ‖exteriorRoots index‖) →
    let r : ℝ := commensurateRadius15308 q
    let P := originalCommensuratePolynomial15308 coefficient r
      zeroMultiplicity interiorRoots exteriorRoots
    let Pcirc := reflectedCommensuratePolynomial15308 coefficient r
      zeroMultiplicity interiorRoots exteriorRoots
    let forced : ℂ := (r : ℂ) ^ 2
    let mass := completeRemovedNumeratorInnerMass15308 q
      zeroMultiplicity interiorRoots
    Pcirc ≠ 0 ∧
      Polynomial.eval forced Pcirc = 0 ∧
      Polynomial.eval forced Pcirc.derivative ≠ 0 ∧
      (∀ w : ℂ, ‖w‖ < r →
        (Polynomial.eval w Pcirc = 0 ↔ w = forced)) ∧
      (∀ w : ℂ, ‖w‖ = r →
        ‖Polynomial.eval w Pcirc‖ = ‖Polynomial.eval w P‖) ∧
      criticalCauchyNorm15308 q Pcirc =
        criticalCauchyNorm15308 q P ∧
      ‖poleCancelledCenterValue15308 q Pcirc‖ =
        Real.exp mass * ‖poleCancelledCenterValue15308 q P‖

end

end MathlibPlus.Open.Analysis.BatchO0313Claim15308
