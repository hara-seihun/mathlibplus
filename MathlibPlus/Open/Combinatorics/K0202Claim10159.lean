import MathlibPlus.Open.Combinatorics.TreeOperators

namespace MathlibPlus.Open.Combinatorics.K0202Claim10159

noncomputable section

/-- Edge subdivision and leaf deletion have the leaf-count commutator on the
actual tree graph carrier; the edge-level clauses record the two local facts
behind the extra pendant-edge copy. -/
def claim10159 : Prop :=
  (∀ k : ℕ, ∀ x : GraphSpace (k + 1),
    x ∈ treeSpace (k + 1) →
      ∀ q : GraphClass (k + 1),
        (L (k + 1) (S (k + 1) x) - S k (L k x)) q =
          (Nat.card {v : Fin (k + 1) //
              isLeaf (graphRep q) v} : ℚ) * x q) ∧
  (∀ n : ℕ, ∀ q : GraphClass n, ∀ e : Sym2 (Fin n),
    (graphRep q).IsTree →
      e ∈ (graphRep q).edgeSet →
        ((∀ v : Fin n,
            isLeaf (graphRep q) v ↔
              isLeaf (subdivideGraph (graphRep q) e) v.castSucc) ∧
          ¬ isLeaf (subdivideGraph (graphRep q) e) (Fin.last n))) ∧
  (∀ n : ℕ, ∀ q : GraphClass n, ∀ e : Sym2 (Fin n),
      ∀ v : Fin n,
    (graphRep q).IsTree →
      e ∈ (graphRep q).edgeSet →
        isLeaf (graphRep q) v →
          (∃ u : Fin n, e = s(v, u) ∧ (graphRep q).Adj v u) →
            graphClass
                (deleteGraph (subdivideGraph (graphRep q) e) v.castSucc) = q)

end

end MathlibPlus.Open.Combinatorics.K0202Claim10159
