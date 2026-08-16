import MathlibPlus.Open.NewResearch2.LimitingResidual15317

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BatchO0313Claim15311

noncomputable section

private def commensurateLog15311 (q : ℤ) : ℝ :=
  Real.log (q : ℝ)

private def commensurateRadius15311 (q : ℤ) : ℝ :=
  Real.rpow (q : ℝ) (-(1 / 2 : ℝ))

private def commensuratePhi15311 (q : ℤ) (z : ℂ) : ℂ :=
  Complex.exp
    (-(((commensurateLog15311 q / 2 : ℝ) : ℂ) *
      ((1 + z) / (1 - z))))

private def linearFactorProduct15311 {Index : Type*} [Fintype Index]
    (roots : Index → ℂ) : Polynomial ℂ :=
  ∏ index, (Polynomial.X - Polynomial.C (roots index))

private def circleReflectedFactor15311 (r : ℝ) (root : ℂ) : Polynomial ℂ :=
  Polynomial.C (r : ℂ) *
    (1 - Polynomial.C (star root / (r : ℂ) ^ 2) * Polynomial.X)

private def reflectedCommensuratePolynomial15311
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient
    * (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2))
    * Polynomial.C ((r : ℂ) ^ zeroMultiplicity)
    * (∏ index, circleReflectedFactor15311 r (interiorRoots index))
    * linearFactorProduct15311 exteriorRoots

private def originalCommensuratePolynomial15311
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient
    * (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2))
    * Polynomial.X ^ zeroMultiplicity
    * linearFactorProduct15311 interiorRoots
    * linearFactorProduct15311 exteriorRoots

private def commensurateOuterPolynomial15311
    (q : ℤ) (Pcirc : Polynomial ℂ) : Polynomial ℂ :=
  let r : ℝ := commensurateRadius15311 q
  (Pcirc.comp (Polynomial.C (r : ℂ) * Polynomial.X)) /ₘ
    (Polynomial.X - Polynomial.C (r : ℂ))

private def commensurateH15311 (q : ℤ) (z : ℂ) : ℂ :=
  let r : ℝ := commensurateRadius15311 q
  MathlibPlus.Open.NewResearch2.LimitingResidual15317.zetaResidual z *
    (1 - (r : ℂ) * commensuratePhi15311 q z) /
      (1 - (r : ℂ) ^ 2)

private def criticalLineBase15311 (q : ℤ) (t : ℝ) : ℂ :=
  commensurateH15311 q
    (1 - 1 / ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))

private def polynomialBoundaryRatio15311
    (q : ℤ) (Q : Polynomial ℂ) (t : ℝ) : ℂ :=
  Polynomial.eval
      (Complex.exp
        (-Complex.I * ((commensurateLog15311 q * t : ℝ) : ℂ))) Q /
    Polynomial.eval (commensurateRadius15311 q : ℂ) Q

/-- Every finite reflected numerator multiplier is a measurable periodic
critical-line multiplier and hence belongs to the stated measurable periodic
relaxation of the fixed residual carrier. -/
def claim15311 : Prop :=
  ∀ (q : ℤ) (Interior Exterior : Type*)
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ),
    (2 : ℤ) ≤ q →
    coefficient ≠ 0 →
    (∀ index,
      interiorRoots index ≠ 0 ∧
        ‖interiorRoots index‖ < commensurateRadius15311 q ∧
        interiorRoots index ≠
          (commensurateRadius15311 q : ℂ) ^ 2) →
    (∀ index, commensurateRadius15311 q ≤ ‖exteriorRoots index‖) →
    let r : ℝ := commensurateRadius15311 q
    let P := originalCommensuratePolynomial15311 coefficient r
      zeroMultiplicity interiorRoots exteriorRoots
    let Pcirc := reflectedCommensuratePolynomial15311 coefficient r
      zeroMultiplicity interiorRoots exteriorRoots
    let Q := commensurateOuterPolynomial15311 q Pcirc
    let ratio : ℝ → ℂ := polynomialBoundaryRatio15311 q Q
    let T : ℝ := 2 * Real.pi / commensurateLog15311 q
    P ≠ 0 ∧
      (∀ u : ℂ, ‖u‖ < 1 → Polynomial.eval u Q ≠ 0) ∧
      Polynomial.eval (r : ℂ) Q ≠ 0 ∧
      Measurable ratio ∧
      Function.Periodic ratio T ∧
      (∃ g : ℝ → ℂ,
        g = ratio ∧
          Measurable g ∧
          Function.Periodic g T ∧
          (∀ t : ℝ,
            criticalLineBase15311 q t * ratio t =
              criticalLineBase15311 q t * g t))

end

end MathlibPlus.Open.Analysis.BatchO0313Claim15311
