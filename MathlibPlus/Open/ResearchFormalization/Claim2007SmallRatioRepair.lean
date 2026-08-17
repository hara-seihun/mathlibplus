import MathlibPlus.Open.Research.FormalizationBatchAnalysis

namespace MathlibPlus.Open.ResearchFormalization.Claim2007

noncomputable section

/-- The exact admissible weight class supplied by the reviewed CHJ carrier. -/
def phaseWeightClass (ξ : ℝ) : Set (ℝ → ℝ) :=
  {w | MathlibPlus.Open.Research.admissiblePhaseWeight ξ w}

/-- Claim 2007: the exact small-ratio infimum and the constant minimizer,
with uniqueness understood on the interval on which the weight is defined. -/
def claim2007_exactSmallRatioInfimumUniqueMinimizer : Prop :=
  ∀ (ξ : ℝ),
    1 < ξ → ξ ≤ MathlibPlus.Open.Research.criticalXi →
      let Wξ : Set (ℝ → ℝ) := phaseWeightClass ξ
      let Aξ : ℝ := MathlibPlus.Open.Research.constantPhaseA ξ
      let w₀ : ℝ → ℝ := fun _ => 1 / (ξ - 1)
      sInf (MathlibPlus.Open.Research.constantPhaseJ ξ '' Wξ) = Aξ ∧
        w₀ ∈ Wξ ∧
        MathlibPlus.Open.Research.constantPhaseJ ξ w₀ = Aξ ∧
        (∀ w : ℝ → ℝ,
          w ∈ Wξ →
          MathlibPlus.Open.Research.constantPhaseJ ξ w = Aξ →
          ∀ u ∈ Set.Icc (1 : ℝ) ξ, w u = w₀ u)

end

end MathlibPlus.Open.ResearchFormalization.Claim2007
