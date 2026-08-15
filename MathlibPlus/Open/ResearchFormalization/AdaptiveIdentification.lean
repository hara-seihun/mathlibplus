import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

open scoped BigOperators

/-- Finite deterministic binary decision trees with coordinate-labelled queries. -/
inductive adaptiveBinaryDecisionTree (I Ω : Type) where
  | leaf (output : Ω)
  | query (coordinate : I)
      (whenNegative whenPositive : adaptiveBinaryDecisionTree I Ω)

/-- Evaluation of a decision tree against a binary coordinate oracle. -/
def adaptiveEvaluate {I Ω : Type} :
    adaptiveBinaryDecisionTree I Ω → (I → Bool) → Ω
  | .leaf output, _ => output
  | .query coordinate whenNegative whenPositive, oracle =>
      if oracle coordinate then
        adaptiveEvaluate whenPositive oracle
      else
        adaptiveEvaluate whenNegative oracle

/-- Maximum number of coordinate queries made on any branch. -/
def adaptiveQueryDepth {I Ω : Type} :
    adaptiveBinaryDecisionTree I Ω → ℕ
  | .leaf _ => 0
  | .query _ whenNegative whenPositive =>
      1 + max (adaptiveQueryDepth whenNegative) (adaptiveQueryDepth whenPositive)

/-- Correctness indicator for a predicted component. -/
noncomputable def adaptiveCorrectIndicator {Ω : Type} (predicted actual : Ω) : ℝ := by
  classical
  exact if predicted = actual then 1 else 0

/-- A finite probability mixture of bounded deterministic binary trees. -/
def adaptiveProbabilityMixture
    {I Ω : Type} (C k R : ℕ)
    (trees : Fin R → adaptiveBinaryDecisionTree I Ω)
    (weights : Fin R → ℝ) : Prop :=
  (∀ r, adaptiveQueryDepth (trees r) ≤ C * k) ∧
    (∀ r, 0 ≤ weights r) ∧
    (∑ r : Fin R, weights r) = 1

/-- Uniform-component, seed-weighted probability of exact identification. -/
noncomputable def adaptiveSuccessProbability
    {I Ω : Type} [Fintype Ω]
    (oracle : Ω → I → Bool)
    {R : ℕ}
    (trees : Fin R → adaptiveBinaryDecisionTree I Ω)
    (weights : Fin R → ℝ) : ℝ :=
  (∑ ω : Ω, ∑ r : Fin R,
      weights r *
        adaptiveCorrectIndicator
          (adaptiveEvaluate (trees r) (oracle ω)) ω) /
    (Fintype.card Ω : ℝ)

/-- The exact adaptive binary-query counting bound and its deterministic corollary. -/
def adaptiveBinaryIdentificationBound : Prop :=
  ∀ (I Ω : Type) [Fintype Ω] [Nonempty Ω],
    ∀ (oracle : Ω → I → Bool) (C k : ℕ),
      (∀ (R : ℕ)
          (trees : Fin R → adaptiveBinaryDecisionTree I Ω)
          (weights : Fin R → ℝ),
        adaptiveProbabilityMixture C k R trees weights →
          adaptiveSuccessProbability oracle trees weights ≤
            ((2 : ℝ) ^ (C * k)) /
              (Fintype.card Ω : ℝ)) ∧
      (Fintype.card Ω > 2 ^ (C * k) →
        ¬ ∃ tree : adaptiveBinaryDecisionTree I Ω,
          adaptiveQueryDepth tree ≤ C * k ∧
            ∀ ω : Ω, adaptiveEvaluate tree (oracle ω) = ω)

end ResearchFormalization
end Open
end MathlibPlus
