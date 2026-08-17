import MathlibPlus.Open.Combinatorics.R1863ReducedPairClaim34318

namespace MathlibPlus.Open.Combinatorics.R1863OrderDegree

open MathlibPlus.Open.Combinatorics.R1863ReducedPair

/-- The rooted host shape with arms of lengths 1, 1, and `l`. -/
def hostShape (l : ℕ) : ShapeTree :=
  ShapeTree.node [arm 1, arm 1, arm l]

/-- Claim 34358: the concrete arm, host, bridge, and reduced-shape orders and
parent/unrooted degree bounds have the stated values. -/
def concreteOrderAndDegreeLemmas_claim34358 : Prop :=
  ∀ (l : ℕ), 3 ≤ l →
    rootedTreeOrder (arm l) = l ∧
      rootedTreeOrder (hostShape l) = l + 3 ∧
      (∀ k : ℕ, rootedTreeOrder (doubleSpiderBridge k) = k + 9) ∧
      rootedTreeOrder (reducedPositiveShape l) = l + 9 ∧
      rootedTreeOrder (reducedNegativeShape l) = l + 9 ∧
      (∀ a : ℕ, unrootedMaximumDegreeWithParent (arm a) ≤ 2) ∧
      (∀ k : ℕ,
        unrootedMaximumDegreeWithParent (doubleSpiderBridge k) ≤ 3) ∧
      unrootedMaximumDegree (reducedPositiveShape l) = 4 ∧
      unrootedMaximumDegree (reducedNegativeShape l) = 3 ∧
      unrootedMaximumDegree (reducedPositiveShape l) ≠
        unrootedMaximumDegree (reducedNegativeShape l)

end MathlibPlus.Open.Combinatorics.R1863OrderDegree
