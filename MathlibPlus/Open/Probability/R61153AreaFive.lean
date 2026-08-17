import MathlibPlus.Open.Probability.DepthTwoOracleSharpFiveFour

namespace MathlibPlus.Open.Probability.R61153AreaFive

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory
open MeasureTheory
open MathlibPlus.Open.Probability

noncomputable section

def depthTwoTreeLaw {I : Type*}
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign)) : Prop :=
  ∀ T ∈ Λ.support,
    ∃ tree : SignDecisionTree I,
      tree.depth ≤ 2 ∧ ∀ O, tree.evaluate O = T O

noncomputable def fixedOrderArea
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign))
    (O : I → Ω → Sign) (P : Measure Ω)
    (order : Fin N → I) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N,
    ∫ ω,
      ProbabilityTheory.condVar
        (revealFiltration O order m)
        (mixtureMean Λ O) P ω ∂P

def fixedOrderContainsActiveCoordinates
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign))
    (O : I → Ω → Sign) (order : Fin N → I) (N : ℕ) : Prop :=
  Function.Injective order ∧
    Set.range order = relevantCoordinates Λ ∧
      @Measurable Ω ℝ
        (revealFiltration O order N) inferInstance (mixtureMean Λ O)

def claim61153 : Prop :=
  ∀ (I : Type*) [Countable I]
    (Λ : FiniteProbabilityLaw ((I → Sign) → Sign)),
    depthTwoTreeLaw Λ →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (O : I → Ω → Sign),
        uniformIndependentSigns P O →
          ∃ (N : ℕ) (order : Fin N → I),
            fixedOrderContainsActiveCoordinates Λ O order N ∧
              fixedOrderArea Λ O P order N ≤ (5 : ℝ)

end
end MathlibPlus.Open.Probability.R61153AreaFive
