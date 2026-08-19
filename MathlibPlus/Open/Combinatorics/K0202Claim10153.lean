import MathlibPlus.Open.Combinatorics.TreeOperators

namespace MathlibPlus.Open.Combinatorics.K0202Claim10153

noncomputable section

open MathlibPlus.Open.Combinatorics

/-- Claim 10153: on the rational graph-isomorphism-class space restricted to
actual tree classes, grafting a new leaf sums over all vertices and leaf
deck deletion sums over exactly the leaf vertices. -/
def leafGraftingAndLeafDeckOperators_claim10153 : Prop :=
  (∀ (n : ℕ) (q : GraphClass n),
    (graphRep q).IsTree →
      G n (Finsupp.single q 1) = graftBasis q) ∧
    (∀ (n : ℕ) (q : GraphClass (n + 1)),
      (graphRep q).IsTree →
        L n (Finsupp.single q 1) = deleteBasis q)

end

end MathlibPlus.Open.Combinatorics.K0202Claim10153
