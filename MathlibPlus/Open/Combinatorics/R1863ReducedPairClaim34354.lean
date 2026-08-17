import MathlibPlus.Open.Combinatorics.R1863ReducedPairClaim34318

namespace MathlibPlus.Open.Combinatorics.R1863ReducedPair

/-- The rooted host spider used in the concrete family. -/
def hostShape (longArm : ℕ) : ShapeTree :=
  ShapeTree.node [arm 1, arm 1, arm longArm]

/-- Claim 34354: the arm, host, reduced positive, bridge, and reduced negative
constructors are the displayed concrete finite rooted-tree shapes. -/
def concreteRootedTreeShapeDefinitions_claim34354 : Prop :=
  (∀ length : ℕ, 1 ≤ length →
    rootedTreeOrder (arm length) = length) ∧
    (∀ longArm : ℕ,
      hostShape longArm =
        ShapeTree.node [arm 1, arm 1, arm longArm]) ∧
    (∀ longArm : ℕ,
      reducedPositiveShape longArm =
        ShapeTree.node [arm 1, arm 1, arm longArm, arm 6]) ∧
    doubleSpiderBridge 0 =
      ShapeTree.node [arm 2, arm 6] ∧
    (∀ step : ℕ,
      doubleSpiderBridge (step + 1) =
        ShapeTree.node [doubleSpiderBridge step]) ∧
    (∀ longArm : ℕ,
      reducedNegativeShape longArm =
        ShapeTree.node [arm 1, arm 1,
          doubleSpiderBridge (longArm - 3)])

end MathlibPlus.Open.Combinatorics.R1863ReducedPair
