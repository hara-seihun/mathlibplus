import Mathlib
import MathlibPlus.Open.Analysis.convolutionOperatorGeometry_claim6971

open scoped BigOperators
open MeasureTheory Set Filter Topology

namespace MathlibPlus.Open.Analysis

noncomputable section

abbrev L2InverseGraphSpace := L2Real × L2Real

def shiftedGammaModulusMultiplier (μ σ t : ℝ) : ℂ :=
  (‖shiftedGammaMultiplier μ σ t‖ : ℂ)

def shiftedGammaPhaseMultiplier (μ σ t : ℝ) : ℂ :=
  shiftedGammaMultiplier μ σ t / shiftedGammaModulusMultiplier μ σ t

def isFourierMultiplierBy
    (F H : L2Real →L[ℂ] L2Real) (m : ℝ → ℂ) : Prop :=
  ∀ f : L2Real,
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      l2Rep (F (H f)) t = m t * l2Rep (F f) t

def sourceConvolutionGeometry (μ σ : ℝ)
    (F G : L2Real →L[ℂ] L2Real) : Prop :=
  IsNoTwoPiFourier F ∧
    IsConvolutionBy μ σ G ∧
    IsFourierMultiplier μ σ F G ∧
    IsBoundedLinearMap ℂ (G : L2Real → L2Real) ∧
    IsStarNormal G ∧
    ‖G‖ = shiftedGammaCReal μ σ ∧
    Function.Injective G ∧
    Set.range (fun f : L2Real => G f) =
      {h : L2Real | shiftedGammaQuotientInL2 μ σ F h} ∧
    Dense (Set.range (fun f : L2Real => G f)) ∧
    Set.range (fun f : L2Real => G f) ≠ Set.univ ∧
    ¬IsClosed (Set.range (fun f : L2Real => G f)) ∧
    ¬IsCompactOperator (G : L2Real →L[ℂ] L2Real) ∧
    ¬IsFredholmL2 G

def inverseMultiplierGraph (μ σ : ℝ)
    (F G : L2Real →L[ℂ] L2Real) : Set L2InverseGraphSpace :=
  {p | p.1 ∈ Set.range (fun f : L2Real => G f) ∧
    G p.2 = p.1 ∧
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      l2Rep (F p.2) t =
        l2Rep (F p.1) t / shiftedGammaMultiplier μ σ t}

def closedDenseUnboundedInverse (μ σ : ℝ)
    (F G : L2Real →L[ℂ] L2Real) : Prop :=
  IsClosed (inverseMultiplierGraph μ σ F G) ∧
    Dense {h : L2Real | ∃ k : L2Real,
      (h, k) ∈ inverseMultiplierGraph μ σ F G} ∧
    {h : L2Real | ∃ k : L2Real,
      (h, k) ∈ inverseMultiplierGraph μ σ F G} =
      Set.range (fun f : L2Real => G f) ∧
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ h k : L2Real,
        (h, k) ∈ inverseMultiplierGraph μ σ F G →
          ‖k‖ ≤ C * ‖h‖

/-- The polar factors and exact inverse graph on the reviewed L²(R) carrier. -/
def polarFactorAndExactInverseDomain_claim6972 : Prop :=
  ∀ μ σ : ℝ, 0 < μ + σ / 2 →
    ∀ F G : L2Real →L[ℂ] L2Real,
      sourceConvolutionGeometry μ σ F G →
        (∀ t : ℝ, shiftedGammaMultiplier μ σ t ≠ 0) ∧
        ∃ (U : L2Real ≃ₗᵢ[ℂ] L2Real)
          (A : L2Real →L[ℂ] L2Real),
          isFourierMultiplierBy F A
              (shiftedGammaModulusMultiplier μ σ) ∧
            isFourierMultiplierBy F
              U.toContinuousLinearEquiv.toContinuousLinearMap
              (shiftedGammaPhaseMultiplier μ σ) ∧
            (G : L2Real →L[ℂ] L2Real) =
              U.toContinuousLinearEquiv.toContinuousLinearMap.comp A ∧
            closedDenseUnboundedInverse μ σ F G

end

end MathlibPlus.Open.Analysis
