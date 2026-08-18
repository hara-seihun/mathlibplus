import MathlibPlus.Open.Combinatorics.TreeOperators

namespace MathlibPlus.Open.ResearchFormalization.K0202Claim10160

noncomputable section

open MathlibPlus.Open.Combinatorics

/-- The leaf-count diagonal used by the subdivision commutator. -/
noncomputable def leafCount10160 {n : ℕ}
    (q : GraphClass n) : ℕ :=
  Nat.card {v : Fin n // isLeaf (graphRep q) v}

/-- Claim 10160: on the actual graph-isomorphism-class tree carrier, the
`αG+βS` diagonal criterion and its support-wise vanishing condition hold. -/
def claim10160 : Prop :=
  ∀ (k : ℕ) (α β : ℚ) (w : GraphSpace (k + 1)),
    w ∈ treeSpace (k + 1) →
      L k w = 0 →
        (∀ q : GraphClass (k + 1),
          (L (k + 1)
              (((α • G (k + 1)) + (β • S (k + 1))) w)) q =
            (α * ((k + 1 : ℕ) : ℚ) +
              β * (leafCount10160 q : ℚ)) * w q) ∧
        ((L (k + 1)
            (((α • G (k + 1)) + (β • S (k + 1))) w)) = 0 ↔
          ∀ q : GraphClass (k + 1),
            w q ≠ 0 →
              α * ((k + 1 : ℕ) : ℚ) +
                β * (leafCount10160 q : ℚ) = 0)

end

end MathlibPlus.Open.ResearchFormalization.K0202Claim10160
