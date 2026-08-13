import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim5039

/-- The Walsh character attached to an edge subset of the complete labelled graph.
The domain condition `hA` records that `A` is a subset of `E(K_n)`; the value is
computed by intersecting it with the edge set of the labelled graph `G`. -/
def walshCharacter (n : ℕ) (A : Finset (Sym2 (Fin n)))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : A ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset) : ℤ :=
  (-1 : ℤ) ^ ((A ∩ G.edgeFinset).card)

end MathlibPlus.Combinatorics.Claim5039
