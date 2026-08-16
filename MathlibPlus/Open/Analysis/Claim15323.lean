import MathlibPlus.Open.NewResearch2.PeriodicZetaFiber15312_15318

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim15323

noncomputable section

open MathlibPlus.Open.NewResearch2.PeriodicZetaFiber

/-- The finite commensurate polynomial multiplier in the `q^{-s}` variable. -/
noncomputable def finiteCommensurateMultiplier
    (q : ℕ) (P : Polynomial ℂ) (s : ℂ) : ℂ :=
  Polynomial.eval (Complex.exp (-s * (qLog q : ℂ))) P

/-- A finite product of linear root factors. -/
noncomputable def linearFactorProduct {Index : Type*} [Fintype Index]
    (roots : Index → ℂ) : Polynomial ℂ :=
  ∏ index, (Polynomial.X - Polynomial.C (roots index))

/-- Circle reflection of a nonzero interior root at radius `r`. -/
noncomputable def circleReflectedFactor (r : ℝ) (root : ℂ) : Polynomial ℂ :=
  Polynomial.C (r : ℂ) *
    (1 - Polynomial.C (star root / (r : ℂ) ^ 2) * Polynomial.X)

/-- The original finite numerator, including the forced root and all
zero-root multiplicity. -/
noncomputable def originalCommensuratePolynomial
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient *
    (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2)) *
    Polynomial.X ^ zeroMultiplicity *
    linearFactorProduct interiorRoots *
    linearFactorProduct exteriorRoots

/-- The fully reflected numerator after replacing the zero-root monomial by
its boundary-equivalent constant. -/
noncomputable def reflectedCommensuratePolynomial
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (r : ℝ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  Polynomial.C coefficient *
    (Polynomial.X - Polynomial.C ((r : ℂ) ^ 2)) *
    Polynomial.C ((r : ℂ) ^ zeroMultiplicity) *
    (∏ index, circleReflectedFactor r (interiorRoots index)) *
    linearFactorProduct exteriorRoots

/-- The zero-free outer polynomial after the forced root is divided out. -/
noncomputable def outerPolynomial
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (q : ℕ) (coefficient : ℂ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Polynomial ℂ :=
  let r : ℝ := qRadius q
  let Pcirc := reflectedCommensuratePolynomial coefficient r zeroMultiplicity
    interiorRoots exteriorRoots
  (Pcirc.comp (Polynomial.C (r : ℂ) * Polynomial.X)) /ₘ
    (Polynomial.X - Polynomial.C (r : ℂ))

/-- The outer admissibility conditions on the polynomial actually produced by
the finite reflected numerator. -/
def admissibleOuterPolynomial (q : ℕ) (Q : Polynomial ℂ) : Prop :=
  (∀ u : ℂ, ‖u‖ < 1 → Polynomial.eval u Q ≠ 0) ∧
    Polynomial.eval (qRadius q : ℂ) Q ≠ 0

/-- The exact finite root and zero-free outer data for a fully inner-divided
commensurate multiplier. -/
def finiteInnerDividedData
    {Interior Exterior : Type*}
    [Fintype Interior] [Fintype Exterior]
    (q : ℕ) (coefficient : ℂ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ) : Prop :=
  2 ≤ q ∧
    coefficient ≠ 0 ∧
      (∀ index,
        interiorRoots index ≠ 0 ∧
          ‖interiorRoots index‖ < qRadius q ∧
          interiorRoots index ≠ (qRadius q : ℂ) ^ 2) ∧
        (∀ index, qRadius q ≤ ‖exteriorRoots index‖) ∧
          admissibleOuterPolynomial q
            (outerPolynomial q coefficient zeroMultiplicity
              interiorRoots exteriorRoots)

/-- The normalized quotient after complete inner division. -/
noncomputable def fullyInnerDividedQuotient
    (q : ℕ) (Q : Polynomial ℂ) (z : ℂ) : ℂ :=
  qResidualDisk q z *
    Polynomial.eval (qPhi q z) Q /
      Polynomial.eval (qRadius q : ℂ) Q

/-- The remaining outer polynomial multiplier on the critical line. -/
noncomputable def outerBoundaryRatio
    (q : ℕ) (Q : Polynomial ℂ) (t : ℝ) : ℂ :=
  Polynomial.eval (qPhi q (qCriticalPoint t)) Q /
    Polynomial.eval (qRadius q : ℂ) Q

noncomputable def quotientBoundary
    (q : ℕ) (Q : Polynomial ℂ) (t : ℝ) : ℂ :=
  qCriticalBase q t * outerBoundaryRatio q Q t

/-- The zero-corrected Hardy mass of the normalized quotient. -/
noncomputable def quotientMass (q : ℕ) (Q : Polynomial ℂ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    ENNReal.ofReal (‖quotientBoundary q Q t‖ ^ 2)
      ∂qCauchyMeasure

/-- The zero-corrected BSY evaluation slack. -/
noncomputable def zeroCorrectedEvaluationSlack
    (q : ℕ) (Q : Polynomial ℂ) : EReal :=
  (1 / 2 : EReal) * ENNReal.log (quotientMass q Q)

/-- The correctly normalized factor left by retaining a zero-root monomial:
relative to the boundary-equivalent constant it is `Phi_q/r`, not `r Phi_q`. -/
noncomputable def retainedZeroSingularFactor
    (q : ℕ) (k : ℕ) (t : ℝ) : ℂ :=
  (qPhi q (qCriticalPoint t) / (qRadius q : ℂ)) ^ k

noncomputable def retainedZeroBoundary
    (q : ℕ) (Q : Polynomial ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  retainedZeroSingularFactor q k t * quotientBoundary q Q t

noncomputable def retainedZeroMass
    (q : ℕ) (Q : Polynomial ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    ENNReal.ofReal (‖retainedZeroBoundary q Q k t‖ ^ 2)
      ∂qCauchyMeasure

noncomputable def retainedZeroEvaluationSlack
    (q : ℕ) (Q : Polynomial ℂ) (k : ℕ) : EReal :=
  (1 / 2 : EReal) * ENNReal.log (retainedZeroMass q Q k)

/-- Claim 15323: every finite fully inner-divided commensurate quotient has
zero-corrected slack at least the exact periodic-fiber floor, uniformly over
its degree, coefficients, and integer base; retaining a zero-root singular
factor only increases the slack. -/
def uniformPositiveBSYEvaluationFloor_claim15323 : Prop :=
  (∀ (q : ℕ) (Interior Exterior : Type*)
    [Fintype Interior] [Fintype Exterior]
    (coefficient : ℂ) (zeroMultiplicity : ℕ)
    (interiorRoots : Interior → ℂ)
    (exteriorRoots : Exterior → ℂ),
    finiteInnerDividedData q coefficient zeroMultiplicity
      interiorRoots exteriorRoots →
      let Q := outerPolynomial q coefficient zeroMultiplicity
        interiorRoots exteriorRoots
      fullyInnerDividedQuotient q Q 0 = 1 ∧
        qPeriodicMultiplier q (outerBoundaryRatio q Q) ∧
        quotientMass q Q =
          1 + qWeightedLoss q (outerBoundaryRatio q Q) ∧
        qDelta q ≤ qWeightedLoss q (outerBoundaryRatio q Q) ∧
        (1 / 2 : EReal) * ENNReal.log (1 + qDelta q) ≤
          zeroCorrectedEvaluationSlack q Q ∧
        (∀ k : ℕ,
          retainedZeroMass q Q k =
            ENNReal.ofReal (Real.exp ((k : ℝ) * qLog q)) *
              quotientMass q Q ∧
          zeroCorrectedEvaluationSlack q Q ≤
            retainedZeroEvaluationSlack q Q k)) ∧
  (∃ ε : EReal, 0 < ε ∧
    ∀ q : ℕ, 2 ≤ q →
      ε ≤ (1 / 2 : EReal) * ENNReal.log (1 + qDelta q))

end

end MathlibPlus.Open.Analysis.Claim15323
