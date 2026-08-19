import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0014f_9da0_7b3c_8e09_26f26436e566

open scoped BigOperators
open BigOperators
open Classical

namespace MathlibPlus.Combinatorics.HordeClaimFormalizations

noncomputable section

abbrev WitnessCoordinate44852 := Fin 4
abbrev WitnessInput44852 := WitnessCoordinate44852 → Bool
abbrev WitnessTree44852 :=
  MathlibPlus.Open.ResearchFormalizationBatch.DecisionTree WitnessCoordinate44852
abbrev WitnessSubset44852 := Finset WitnessCoordinate44852

def signValue44852 (b : Bool) : ℚ := if b then 1 else -1

def witnessTree44852 : WitnessTree44852 :=
  .query 0
    (.leaf true)
    (.query 2
      (.leaf false)
      (.query 3 (.leaf true) (.leaf false)))

def treeDepth44852 : WitnessTree44852 → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max (treeDepth44852 negative) (treeDepth44852 positive)

def witnessValue44852 (ω : WitnessInput44852) : ℚ :=
  signValue44852
    (MathlibPlus.Open.ResearchFormalizationBatch.DecisionTree.evaluate
      witnessTree44852 ω)

def queriedPath44852 (ω : WitnessInput44852) : Finset WitnessCoordinate44852 :=
  Finset.univ.filter (fun i =>
    MathlibPlus.Open.ResearchFormalizationBatch.DecisionTree.queried
      witnessTree44852 i ω)

def pathProbability44852 (S : WitnessSubset44852) : ℚ :=
  (∑ ω : WitnessInput44852,
      if S ⊆ queriedPath44852 ω then 1 else 0) /
    (Fintype.card WitnessInput44852 : ℚ)

def character44852 (S : WitnessSubset44852) (ω : WitnessInput44852) : ℚ :=
  ∏ i ∈ S, signValue44852 (ω i)

def fourierCoefficient44852 (S : WitnessSubset44852) : ℚ :=
  (∑ ω : WitnessInput44852,
      witnessValue44852 ω * character44852 S ω) /
    (Fintype.card WitnessInput44852 : ℚ)

def pathFourierCoefficient44852 (S : WitnessSubset44852) : ℚ :=
  (∑ ω : WitnessInput44852,
      witnessValue44852 ω * character44852 S ω *
        (if S ⊆ queriedPath44852 ω then 1 else 0)) /
    (Fintype.card WitnessInput44852 : ℚ)

def pathContainmentCharge44852 : ℚ :=
  ∑ S ∈ (Finset.univ.filter Finset.Nonempty),
    fourierCoefficient44852 S ^ 2 / pathProbability44852 S

def expectedQueriedPathSize44852 : ℚ :=
  (∑ ω : WitnessInput44852, (queriedPath44852 ω).card) /
    (Fintype.card WitnessInput44852 : ℚ)

/-- Claim 44852: the explicit depth-three adaptive tree has the exact
path-containment Fourier charge and expected queried-path size, and therefore
is a counterexample to the proposed universal inequality. -/
def explicitDepthThreeBooleanTreeCounterexample_claim44852 : Prop :=
  treeDepth44852 witnessTree44852 = 3 ∧
    pathContainmentCharge44852 = 29 / 16 ∧
    expectedQueriedPathSize44852 = 7 / 4 ∧
    (∀ S : WitnessSubset44852,
      fourierCoefficient44852 S = pathFourierCoefficient44852 S) ∧
    pathContainmentCharge44852 - expectedQueriedPathSize44852 = 1 / 16 ∧
    ¬ pathContainmentCharge44852 ≤ expectedQueriedPathSize44852

end

end MathlibPlus.Combinatorics.HordeClaimFormalizations
