import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CommonFactor15394

noncomputable section

/-- The noncommon-zero chart used by the projective coordinate. -/
def commonNonvanishingChart (U : Set ℂ) (X D : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ U ∧ X z ≠ 0 ∧ D z ≠ 0}

/-- The projective shadow coordinate `Π = -X / D`. -/
noncomputable def projectiveRatio (X D : ℂ → ℂ) (z : ℂ) : ℂ :=
  -X z / D z

/-- The logarithmic derivative of the projective coordinate. -/
noncomputable def projectiveLogarithmicDerivative
    (X D : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (projectiveRatio X D) z / projectiveRatio X D z

/-- The carrier-difference form of the same logarithmic derivative. -/
noncomputable def logarithmicDerivativeDifference
    (X D : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv X z / X z - deriv D z / D z

/-- The regular Stokes graph: the regular part of the level `log |Π| = 0`. -/
noncomputable def regularStokesGraph
    (U : Set ℂ) (X D : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ commonNonvanishingChart U X D ∧
    Real.log ‖projectiveRatio X D z‖ = 0 ∧
    projectiveLogarithmicDerivative X D z ≠ 0}

/-- Phase speed on a regular Stokes graph. -/
noncomputable def projectivePhaseSpeed
    (X D : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖projectiveLogarithmicDerivative X D z‖

/-- The phase flux along a parametrized arc, `∫ |ω(z)| |dz|`. -/
noncomputable def projectivePhaseFlux
    (X D : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ s in Set.Icc a b,
    projectivePhaseSpeed X D (γ s) * ‖deriv γ s‖

/--
Claim 15394: a nowhere-zero holomorphic common factor preserves the exact
projective ratio, its logarithmic derivative, the regular Stokes graph, and
projective phase flux.  The constant nonzero specialization includes common
scalar signs and amplitudes and preserves phase speed.
-/
def commonFactorInvariance_claim15394 : Prop :=
  ∀ (U : Set ℂ) (X D H : ℂ → ℂ),
    IsOpen U →
    IsConnected U →
    DifferentiableOn ℂ X U →
    DifferentiableOn ℂ D U →
    DifferentiableOn ℂ H U →
    (∀ z : ℂ, z ∈ U → H z ≠ 0) →
    let XH : ℂ → ℂ := fun z => H z * X z
    let DH : ℂ → ℂ := fun z => H z * D z
    (commonNonvanishingChart U XH DH =
        commonNonvanishingChart U X D) ∧
      (∀ z : ℂ, z ∈ commonNonvanishingChart U X D →
        projectiveRatio XH DH z = projectiveRatio X D z ∧
        projectiveLogarithmicDerivative XH DH z =
          projectiveLogarithmicDerivative X D z ∧
        logarithmicDerivativeDifference XH DH z =
          logarithmicDerivativeDifference X D z ∧
        projectiveLogarithmicDerivative X D z =
          logarithmicDerivativeDifference X D z ∧
        projectiveLogarithmicDerivative XH DH z =
          logarithmicDerivativeDifference XH DH z ∧
        projectivePhaseSpeed XH DH z = projectivePhaseSpeed X D z) ∧
      regularStokesGraph U XH DH = regularStokesGraph U X D ∧
      (∀ (γ : ℝ → ℂ) (a b : ℝ),
        (∀ s : ℝ, s ∈ Set.Icc a b →
          γ s ∈ regularStokesGraph U X D) →
        projectivePhaseFlux XH DH γ a b =
          projectivePhaseFlux X D γ a b) ∧
      (∀ c : ℂ, c ≠ 0 →
        let Xc : ℂ → ℂ := fun z => c * X z
        let Dc : ℂ → ℂ := fun z => c * D z
        ∀ z : ℂ, z ∈ commonNonvanishingChart U X D →
          projectivePhaseSpeed Xc Dc z = projectivePhaseSpeed X D z)

end

end MathlibPlus.Open.ResearchFormalization.CommonFactor15394
