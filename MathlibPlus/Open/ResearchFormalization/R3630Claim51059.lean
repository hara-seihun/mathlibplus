import MathlibPlus.Open.ResearchFormalization.R3630

open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MathlibPlus.Open.ResearchFormalization.R3630Claim51059

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R3630

/-- Covariance computed with the uniform measure on one transcript cell. -/
noncomputable def cellCovariance {n : ℕ}
    (f g : RademacherCube n → ℝ)
    (cell : Finset (RademacherCube n)) : ℝ :=
  realConditionalMean (fun x => f x * g x) cell -
    realConditionalMean f cell * realConditionalMean g cell

/-- The conditional probability of a descendant transcript inside a cell. -/
noncomputable def relativeNodeProbability {n : ℕ}
    (tree : DecisionTree n) (cellPath path : List Bool) : ℝ :=
  ((transcriptCell tree path).card : ℝ) /
    ((transcriptCell tree cellPath).card : ℝ)

/-- Internal nodes below a fixed transcript cell. -/
def cellInternalPaths {n : ℕ}
    (tree : DecisionTree n) (cellPath : List Bool) :
    Finset (List Bool) :=
  tree.internalPaths.filter (fun path => List.IsPrefix cellPath path)

/-- Claim 51059: the finite node-Haar expansion, its global covariance
identity, and the same identity after conditioning on every transcript cell. -/
def claim51059 : Prop :=
  ∀ (n : ℕ) (h : BooleanFunction n) (tree : DecisionTree n)
    (z : RademacherCube n → ℝ),
    validDeterminingTree h tree →
      (∀ x : RademacherCube n,
        h.1 x - uniformMean h.1 =
          ∑ path ∈ tree.internalPaths,
            treeHaarPacket tree h.1 path x) ∧
      cubeCovariance h.1 z =
        ∑ path ∈ tree.internalPaths,
          nodeProbability tree path *
            realNodeHalfDifference h.1 tree path *
            realNodeHalfDifference z tree path ∧
      (∀ cellPath ∈ tree.nodePaths,
        cellCovariance h.1 z (transcriptCell tree cellPath) =
          ∑ path ∈ cellInternalPaths tree cellPath,
            relativeNodeProbability tree cellPath path *
              realNodeHalfDifference h.1 tree path *
              realNodeHalfDifference z tree path)

end

end MathlibPlus.Open.ResearchFormalization.R3630Claim51059
