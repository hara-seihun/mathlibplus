import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatch
import MathlibPlus.Analysis.ReciprocalXi

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0268Claim15182

noncomputable section

private def admissibleProfile
    (k : ℕ) (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ) : Prop :=
  1 ≤ k ∧
    (∀ L : ℝ, 1 ≤ B L) ∧
    (∀ L : ℝ,
      P L = 1 + ∑ j ∈ Finset.Icc 1 (d L),
        Polynomial.monomial j (coeff L j)) ∧
    (∀ (L : ℝ) (j : ℕ), j ∈ Finset.Icc 1 (d L) →
      ‖coeff L j‖ ≤ (B L) ^ j) ∧
    Tendsto (fun L : ℝ => (B L) ^ k * (d L : ℝ) / L)
      atTop (𝓝 0) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ) * Real.log (B L))
      (fun L : ℝ => L)

private noncomputable def xiPlane (z : ℂ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + Complex.I * z)

private noncomputable def profileValue
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  (P L).eval
    (z ^ 2 / (Real.rpow L (1 / (k : ℝ)) : ℂ))

private noncomputable def profileCarrier
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  xiPlane z / (2 * (Real.pi : ℂ)) * profileValue P k L z

private noncomputable def diniCarrier (L : ℝ) (z : ℂ) : ℂ :=
  (z * Complex.sin ((L : ℂ) * z) -
      (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 + (1 / 4 : ℂ))

private noncomputable def ghatCarrier (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (L : ℂ) * z) * diniCarrier L z

private noncomputable def actionConstant
    (amplification : ℝ → ℝ) (L : ℝ) : ℝ :=
  MathlibPlus.Open.Analysis.FormalizationBatch.movingActionConstant
    amplification L

private noncomputable def transitionScale (k : ℕ) (L : ℝ) : ℝ :=
  Real.rpow L (1 / (2 * (k : ℝ)))

private noncomputable def movingKappa
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (L y : ℝ) : ℝ :=
  Real.rpow
    ((actionConstant amplification L - y) / alpha)
    (1 / (2 * (k : ℝ)))

private noncomputable def graphPoint
    (k : ℕ) (kappa y L : ℝ) : ℂ :=
  (kappa * transitionScale k L : ℂ) +
    (y : ℂ) * Complex.I

private noncomputable def leadingAction
    (k : ℕ) (alpha A L : ℝ) (z : ℂ) : ℂ :=
  (alpha : ℂ) * z ^ (2 * k) -
    Complex.I * (L : ℂ) * z - ((A * L : ℝ) : ℂ)

private noncomputable def logarithmicCoordinate
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  leadingAction k alpha (actionConstant amplification L) L z -
    Complex.log (profileCarrier P k L z / ghatCarrier L z)

private noncomputable def modelFunction
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  profileCarrier P k L z *
      Complex.exp (-(alpha : ℂ) * z ^ (2 * k)) -
    (amplification L * Real.exp (-5 * L / 2) : ℂ) *
      diniCarrier L z

private noncomputable def counterfeitMultiplier (R : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 4 / (R : ℂ) ^ 4

private noncomputable def counterfeitDivisors (R : ℝ) : Set ℂ :=
  {z : ℂ | counterfeitMultiplier R z = 0}

private noncomputable def counterfeitModelFunction
    (R : ℝ) (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  (counterfeitMultiplier R z * profileCarrier P k L z) *
      Complex.exp (-(alpha : ℂ) * z ^ (2 * k)) -
    (amplification L * Real.exp (-5 * L / 2) : ℂ) *
      diniCarrier L z

private noncomputable def counterfeitCoordinate
    (R : ℝ) (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  leadingAction k alpha (actionConstant amplification L) L z -
    Complex.log
      ((counterfeitMultiplier R z * profileCarrier P k L z) /
        ghatCarrier L z)

private noncomputable def conformalDerivative
    (k : ℕ) (alpha : ℝ) (P : ℝ → Polynomial ℂ)
    (L : ℝ) (z : ℂ) : ℂ :=
  (2 * (k : ℂ)) * (alpha : ℂ) * z ^ (2 * k - 1) -
      Complex.I * (L : ℂ) -
    deriv (fun w : ℂ => profileCarrier P k L w) z /
      profileCarrier P k L z +
    deriv (fun w : ℂ => ghatCarrier L w) z /
      ghatCarrier L z

private noncomputable def counterfeitConformalDerivative
    (R : ℝ) (k : ℕ) (alpha : ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  (2 * (k : ℂ)) * (alpha : ℂ) * z ^ (2 * k - 1) -
      Complex.I * (L : ℂ) -
    deriv (fun w : ℂ =>
      counterfeitMultiplier R w * profileCarrier P k L w) z /
      (counterfeitMultiplier R z * profileCarrier P k L z) +
    deriv (fun w : ℂ => ghatCarrier L w) z /
      ghatCarrier L z

private noncomputable def baseActionError
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L kappa y : ℝ) : ℝ :=
  (logarithmicCoordinate k alpha amplification P L
      (graphPoint k kappa y L)).re -
    L * (alpha * kappa ^ (2 * k) + y -
      actionConstant amplification L)

private noncomputable def counterfeitActionError
    (R : ℝ) (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L kappa y : ℝ) : ℝ :=
  (counterfeitCoordinate R k alpha amplification P L
      (graphPoint k kappa y L)).re -
    L * (alpha * kappa ^ (2 * k) + y -
      actionConstant amplification L)

private noncomputable def movingRectangle
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (y₀ y₁ L : ℝ) : Set ℂ :=
  {z : ℂ |
    movingKappa k alpha amplification L y₁ * transitionScale k L ≤ z.re ∧
      z.re ≤ movingKappa k alpha amplification L y₀ * transitionScale k L ∧
      y₀ ≤ z.im ∧ z.im ≤ y₁}

private noncomputable def zeroMultiplicity
    (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  if f z = 0 then (meromorphicOrderAt f z).untop₀.toNat else 0

private def countedZeroSet (f : ℂ → ℂ) (region : Set ℂ) : Set (ℂ × ℕ) :=
  {p | p.1 ∈ region ∧ p.2 < zeroMultiplicity f p.1}

private noncomputable def zeroCount
    (f : ℂ → ℂ) (region : Set ℂ) : ℕ :=
  (countedZeroSet f region).ncard

private def latticeValue (psi : ℂ) : Prop :=
  ∃ m : ℤ,
    psi = (2 * (Real.pi : ℂ)) * Complex.I * (m : ℂ)

/-- Claim 15182: the quartic carrier counterfeit adds four divisors while the
exact leading action, conformal derivative, lattice relation, and item-6
positive-density train remain the same at leading order. -/
def claim15182 : Prop :=
  ∀ (R : ℝ) (k : ℕ) (alpha : ℝ)
    (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ)
    (y₀ y₁ : ℝ),
    R ≠ 0 →
      admissibleProfile k P d B coeff →
      0 < alpha →
      (∀ L : ℝ, 1 ≤ amplification L) →
      Tendsto (fun L : ℝ => amplification L * Real.exp (-2 * L))
        atTop (𝓝 0) →
      0 < y₀ → y₀ < y₁ → y₁ < (1 : ℝ) / 2 →
      MathlibPlus.Open.Analysis.FormalizationBatch.movingActionConstantBounds
        amplification y₀ y₁ →
      let q : ℝ := 1 / (2 * (k : ℝ))
      let kappa : ℝ → ℝ → ℝ := fun L y =>
        Real.rpow ((actionConstant amplification L - y) / alpha) q
      let densityScale : ℝ → ℝ := fun L => Real.rpow L (1 + q)
      let density : ℝ → ℝ := fun L =>
        (kappa L y₀ - kappa L y₁) / (2 * Real.pi)
      let baseCount : ℝ → ℕ := fun L =>
        zeroCount (modelFunction k alpha amplification P L)
          (movingRectangle k alpha amplification y₀ y₁ L)
      let counterfeitCount : ℝ → ℕ := fun L =>
        zeroCount
          (counterfeitModelFunction R k alpha amplification P L)
          (movingRectangle k alpha amplification y₀ y₁ L)
      (Set.Finite (counterfeitDivisors R) ∧
          (counterfeitDivisors R).ncard = 4) ∧
      (∀ L : ℝ,
        {z : ℂ |
            counterfeitMultiplier R z * profileCarrier P k L z = 0} =
          {z : ℂ | profileCarrier P k L z = 0} ∪
            counterfeitDivisors R) ∧
      (∃ c C : ℝ,
        0 < c ∧ c < C ∧
        (∀ᶠ L : ℝ in atTop,
          ∀ y ∈ Set.Icc y₀ y₁,
            c ≤ kappa L y ∧ kappa L y ≤ C) ∧
        (∀ kappaValue ∈ Set.Icc c C,
          ∀ y ∈ Set.Icc y₀ y₁,
            (∃ error : ℝ → ℝ,
              Tendsto error atTop (𝓝 0) ∧
                ∀ᶠ L : ℝ in atTop,
                  (profileCarrier P k L
                      (graphPoint k kappaValue y L) ≠ 0 ∧
                    ghatCarrier L
                      (graphPoint k kappaValue y L) ≠ 0 →
                    baseActionError k alpha amplification P L
                        kappaValue y = L * error L)) ∧
            (∃ error : ℝ → ℝ,
              Tendsto error atTop (𝓝 0) ∧
                ∀ᶠ L : ℝ in atTop,
                  (counterfeitMultiplier R
                      (graphPoint k kappaValue y L) ≠ 0 ∧
                    profileCarrier P k L
                      (graphPoint k kappaValue y L) ≠ 0 ∧
                    ghatCarrier L
                      (graphPoint k kappaValue y L) ≠ 0 →
                    counterfeitActionError R k alpha amplification P L
                        kappaValue y = L * error L)) ∧
            (∃ error : ℝ → ℂ,
              Tendsto error atTop (𝓝 0) ∧
                ∀ᶠ L : ℝ in atTop,
                  (profileCarrier P k L
                      (graphPoint k kappaValue y L) ≠ 0 ∧
                    ghatCarrier L
                      (graphPoint k kappaValue y L) ≠ 0 →
                    conformalDerivative k alpha P L
                        (graphPoint k kappaValue y L) +
                        Complex.I * (L : ℂ) =
                      (L : ℂ) * error L)) ∧
            (∃ error : ℝ → ℂ,
              Tendsto error atTop (𝓝 0) ∧
                ∀ᶠ L : ℝ in atTop,
                  (counterfeitMultiplier R
                      (graphPoint k kappaValue y L) ≠ 0 ∧
                    profileCarrier P k L
                      (graphPoint k kappaValue y L) ≠ 0 ∧
                    ghatCarrier L
                      (graphPoint k kappaValue y L) ≠ 0 →
                    counterfeitConformalDerivative R k alpha P L
                        (graphPoint k kappaValue y L) +
                        Complex.I * (L : ℂ) =
                      (L : ℂ) * error L)) ∧
            (∃ error : ℝ → ℂ,
              Tendsto error atTop (𝓝 0) ∧
                ∀ᶠ L : ℝ in atTop,
                  counterfeitMultiplier R
                      (graphPoint k kappaValue y L) ≠ 0 →
                    counterfeitConformalDerivative R k alpha P L
                        (graphPoint k kappaValue y L) -
                      conformalDerivative k alpha P L
                        (graphPoint k kappaValue y L) =
                      (L : ℂ) * error L)) ∧
      (∀ L : ℝ, ∀ z : ℂ,
        profileCarrier P k L z ≠ 0 →
        ghatCarrier L z ≠ 0 →
        (deriv (fun w : ℂ =>
            logarithmicCoordinate k alpha amplification P L w) z =
          conformalDerivative k alpha P L z) ∧
        (counterfeitMultiplier R z ≠ 0 →
          (deriv (fun w : ℂ =>
              counterfeitCoordinate R k alpha amplification P L w) z =
            counterfeitConformalDerivative R k alpha P L z) ∧
          (counterfeitConformalDerivative R k alpha P L z =
            conformalDerivative k alpha P L z -
              deriv (counterfeitMultiplier R) z /
                counterfeitMultiplier R z))) ∧
      (∀ L : ℝ, ∀ z : ℂ,
        profileCarrier P k L z ≠ 0 →
        ghatCarrier L z ≠ 0 →
        (modelFunction k alpha amplification P L z = 0 ↔
          latticeValue
            (logarithmicCoordinate k alpha amplification P L z)) ∧
        (counterfeitMultiplier R z ≠ 0 →
          (counterfeitModelFunction R k alpha amplification P L z = 0 ↔
            latticeValue
              (counterfeitCoordinate R k alpha amplification P L z)))) ∧
      Filter.liminf
          (fun L : ℝ => (baseCount L : ℝ) / densityScale L) atTop ≥
        Filter.liminf (fun L : ℝ => density L) atTop ∧
      Filter.liminf
          (fun L : ℝ => (counterfeitCount L : ℝ) / densityScale L) atTop ≥
        Filter.liminf (fun L : ℝ => density L) atTop ∧
      0 < Filter.liminf (fun L : ℝ => density L) atTop ∧
      (∀ᶠ L : ℝ in atTop,
        ∀ z : ℂ,
          z ∈ movingRectangle k alpha amplification y₀ y₁ L →
            (modelFunction k alpha amplification P L z = 0 →
                z.im ≠ 0) ∧
            (counterfeitModelFunction R k alpha amplification P L z = 0 →
                z.im ≠ 0)))

end

end MathlibPlus.Open.ResearchFormalization.O0268Claim15182
