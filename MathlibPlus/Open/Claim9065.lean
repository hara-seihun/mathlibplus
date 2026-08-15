import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators

namespace Claim9065

abbrev Vertex (n : ℕ) := Fin n

/-- The Boolean value of an edge variable on a simple graph. -/
noncomputable def edgeIndicator {n : ℕ} (X : SimpleGraph (Vertex n)) (e : Sym2 (Vertex n)) : ℤ := by
  classical
  exact if e ∈ X.edgeSet then 1 else 0

noncomputable def edgeFinsetOf {n : ℕ} (G : SimpleGraph (Vertex n)) : Finset (Sym2 (Vertex n)) := by
  classical
  letI := Fintype.ofFinite G.edgeSet
  exact G.edgeFinset

/-- The distinct labeled copies of `G` on its fixed vertex set. -/
noncomputable def labeledCopies (G : SimpleGraph (Vertex n)) : Finset (SimpleGraph (Vertex n)) := by
  classical
  exact Finset.univ.image (fun σ : Equiv.Perm (Vertex n) => SimpleGraph.map (σ : Vertex n → Vertex n) G)

/-- The orbit sum of the edge monomials of the distinct labeled copies of `G`. -/
noncomputable def spanningSubgraphCountOrbitSum (G X : SimpleGraph (Vertex n)) : ℤ :=
  Finset.sum (labeledCopies G) (fun Gcopy =>
    Finset.prod (edgeFinsetOf Gcopy) (fun e => edgeIndicator X e))

/-- The automorphisms of `G`, viewed as a finite set of vertex permutations. -/
noncomputable def automorphisms (G : SimpleGraph (Vertex n)) : Finset (Equiv.Perm (Vertex n)) := by
  classical
  exact Finset.univ.filter (fun σ => SimpleGraph.map (σ : Vertex n → Vertex n) G = G)

/-- The number of distinct labeled copies, `n! / |Aut(G)|`. -/
noncomputable def labeledCopyNumber (G : SimpleGraph (Vertex n)) : ℕ :=
  Nat.factorial n / (automorphisms G).card

/-- The number of edges of `G`, regarded as an integer. -/
noncomputable def edgeNumber (G : SimpleGraph (Vertex n)) : ℤ :=
  (edgeFinsetOf G).card

/-- The sum of all Boolean edge variables of the complete graph on the fixed vertex set. -/
noncomputable def completeEdgeSum (X : SimpleGraph (Vertex n)) : ℤ :=
  Finset.sum (edgeFinsetOf (SimpleGraph.completeGraph (Vertex n))) (fun e => edgeIndicator X e)

/-- The linearly corrected Boolean graph identifier from the admitted claim. -/
noncomputable def graphIdentifier (G X : SimpleGraph (Vertex n)) : ℤ :=
  -1 + spanningSubgraphCountOrbitSum G X +
    ((labeledCopyNumber G + 1 : ℕ) : ℤ) *
      (edgeNumber G - completeEdgeSum X)

/-- Exact zero set of the identifier. -/
def claim_9065_exact_zero_set : Prop :=
  ∀ (n : ℕ) (G H : SimpleGraph (Vertex n)),
    graphIdentifier G H = 0 ↔ Nonempty (H ≃g G)

end Claim9065

end MathlibPlus.Open
