import MathlibPlus.Open.NewResearch2.LimitingResidual15317

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BatchO0313Claim15310

noncomputable section

private def commensurateLog15310 (q : ℤ) : ℝ :=
  Real.log (q : ℝ)

private def commensurateRadius15310 (q : ℤ) : ℝ :=
  Real.rpow (q : ℝ) (-(1 / 2 : ℝ))

private def commensuratePhi15310 (q : ℤ) (z : ℂ) : ℂ :=
  Complex.exp
    (-(((commensurateLog15310 q / 2 : ℝ) : ℂ) *
      ((1 + z) / (1 - z))))

private def linearFactorProduct15310 {Index : Type*} [Fintype Index]
    (roots : Index → ℂ) : Polynomial ℂ :=
  ∏ index, (Polynomial.X - Polynomial.C (roots index))

private def circleReflectedFactor15310 (r : ℝ) (root : ℂ) : Polynomial ℂ :=
  Polynomial.C (r : ℂ) *
    (1 - Polynomial.C (star root / (r : ℂ) ^ 2) * Polynomial.X)

private def originalCommensuratePolynomial15310
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient
    * (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2))
    * Polynomial.X ^ zeroMultiplicity
    * linearFactorProduct15310 interiorRoots
    * linearFactorProduct15310 exteriorRoots

private def reflectedCommensuratePolynomial15310
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient
    * (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2))
    * Polynomial.C ((r : ℂ) ^ zeroMultiplicity)
    * (∏ index, circleReflectedFactor15310 r (interiorRoots index))
    * linearFactorProduct15310 exteriorRoots

private def commensurateOuterPolynomial15310
    (q : ℤ) (Pcirc : Polynomial ℂ) : Polynomial ℂ :=
  let r : ℝ := commensurateRadius15310 q
  (Pcirc.comp (Polynomial.C (r : ℂ) * Polynomial.X)) /ₘ
    (Polynomial.X - Polynomial.C (r : ℂ))

private def commensurateH15310 (q : ℤ) (z : ℂ) : ℂ :=
  let r : ℝ := commensurateRadius15310 q
  MathlibPlus.Open.NewResearch2.LimitingResidual15317.zetaResidual z *
    (1 - (r : ℂ) * commensuratePhi15310 q z) /
      (1 - (r : ℂ) ^ 2)

private def normalizedQuotient15310
    (q : ℤ) (Pcirc : Polynomial ℂ) (z : ℂ) : ℂ :=
  let r : ℝ := commensurateRadius15310 q
  let D : Polynomial ℂ :=
    Pcirc /ₘ (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2))
  let numerator : ℂ :=
    (r : ℂ) *
      MathlibPlus.Open.NewResearch2.LimitingResidual15317.zetaResidual z *
      (1 - (r : ℂ) * commensuratePhi15310 q z) *
      Polynomial.eval ((r : ℂ) * commensuratePhi15310 q z) D
  let denominator : ℂ :=
    (r : ℂ) * (1 - (r : ℂ) ^ 2) *
      Polynomial.eval ((r : ℂ) ^ 2) D
  numerator / denominator

/-- After all numerator inner factors are divided, the normalized quotient is
exactly the residual base times a zero-free outer polynomial multiplier. -/
def claim15310 : Prop :=
  ∀ (q : ℤ) (Interior Exterior : Type*)
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ),
    (2 : ℤ) ≤ q →
    coefficient ≠ 0 →
    (∀ index,
      interiorRoots index ≠ 0 ∧
        ‖interiorRoots index‖ < commensurateRadius15310 q ∧
        interiorRoots index ≠
          (commensurateRadius15310 q : ℂ) ^ 2) →
    (∀ index, commensurateRadius15310 q ≤ ‖exteriorRoots index‖) →
    let r : ℝ := commensurateRadius15310 q
    let P := originalCommensuratePolynomial15310 coefficient r
      zeroMultiplicity interiorRoots exteriorRoots
    let Pcirc := reflectedCommensuratePolynomial15310 coefficient r
      zeroMultiplicity interiorRoots exteriorRoots
    let Q := commensurateOuterPolynomial15310 q Pcirc
    let G := normalizedQuotient15310 q Pcirc
    P ≠ 0 ∧
      (∀ u : ℂ, ‖u‖ < 1 → Polynomial.eval u Q ≠ 0) ∧
      Polynomial.eval (r : ℂ) Q ≠ 0 ∧
      MathlibPlus.Open.NewResearch2.LimitingResidual15317.zetaResidual 0 =
        1 ∧
      commensurateH15310 q 0 = 1 ∧
      G 0 = 1 ∧
      (∀ z : ℂ,
        G z =
          commensurateH15310 q z *
            Polynomial.eval (commensuratePhi15310 q z) Q /
              Polynomial.eval (r : ℂ) Q)

end

end MathlibPlus.Open.Analysis.BatchO0313Claim15310
