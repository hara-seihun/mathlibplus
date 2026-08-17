import MathlibPlus.Open.Research.GramExactBatch

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13497

noncomputable section

abbrev QIndex := MathlibPlus.Open.Research.QIndex
abbrev QMatrix := MathlibPlus.Open.Research.QMatrix

open MathlibPlus.Open.Research
open MathlibPlus.Open.Research.GramExactBatch

/-- Conjugation by one of the four local product unitaries. -/
def productUnitaryConjugation (U A : QMatrix) : QMatrix :=
  U * A * Matrix.conjTranspose U

/-- The local Klein-four twirl by the explicitly named product unitaries
`II`, `XX`, `ZY`, and `YZ`. -/
def localKleinFourTwirl (A : QMatrix) : QMatrix :=
  (1 / 4 : ℂ) •
    (A +
      productUnitaryConjugation (tensor pauliX pauliX) A +
      productUnitaryConjugation (tensor pauliZ pauliY) A +
      productUnitaryConjugation (tensor pauliY pauliZ) A)

/-- The properties required of a successful full-kernel completion. -/
def successfulCompletion13497 (A : QMatrix) : Prop :=
  positiveSemidefinite A ∧
    positiveSemidefinite (partialTranspose A) ∧
      separableGram A ∧ splitLocalGram A

/-- Claim 13497: the concrete local Klein-four twirl fixes the visible row,
annihilates the six invisible gauges, retains only `t Y ⊗ Z`, preserves all
listed positivity/PPT/separability properties, and gives an exact completion
reduction in both directions. -/
def claim13497 : Prop :=
  ∀ (x g : ℝ),
    localKleinFourTwirl (visibleGram x g) = visibleGram x g ∧
      (∀ k : Fin 7, k ≠ (3 : Fin 7) →
        localKleinFourTwirl (nullBasis k) = 0) ∧
      localKleinFourTwirl (nullBasis (3 : Fin 7)) = nullBasis (3 : Fin 7) ∧
      (∀ c : Fin 7 → ℝ,
        localKleinFourTwirl (visibleGram x g + nullCombination c) =
          qFamily x g (c (3 : Fin 7))) ∧
      (∀ t : ℝ,
        localKleinFourTwirl (qFamily x g t) = qFamily x g t) ∧
      (∀ A : QMatrix,
        positiveSemidefinite A →
          positiveSemidefinite (localKleinFourTwirl A)) ∧
      (∀ A : QMatrix,
        positiveSemidefinite (partialTranspose A) →
          positiveSemidefinite (partialTranspose (localKleinFourTwirl A))) ∧
      (∀ A : QMatrix,
        separableGram A → separableGram (localKleinFourTwirl A)) ∧
      (∀ A : QMatrix,
        splitLocalGram A → splitLocalGram (localKleinFourTwirl A)) ∧
      ((∃ c : Fin 7 → ℝ,
          successfulCompletion13497 (visibleGram x g + nullCombination c)) ↔
        ∃ t : ℝ, successfulCompletion13497 (qFamily x g t))

end

end MathlibPlus.Open.ResearchFormalization.O0091Claim13497
