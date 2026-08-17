import MathlibPlus.Open.Combinatorics.TreeDeck

namespace MathlibPlus.Combinatorics.Claim5086

open ProjectsResearch.TreeDeck

private lemma path3_edgeSet : (SimpleGraph.pathGraph 3).edgeSet =
    {Sym2.mk (0 : Fin 3) 1, Sym2.mk (1 : Fin 3) 2} := by
  ext e
  refine Sym2.inductionOn e ?_
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj]

private lemma path4_edgeSet : (SimpleGraph.pathGraph 4).edgeSet =
    {Sym2.mk (0 : Fin 4) 1, Sym2.mk (1 : Fin 4) 2, Sym2.mk (2 : Fin 4) 3} := by
  ext e
  refine Sym2.inductionOn e ?_
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj]

private noncomputable def p3Tree : UnlabelledTree 3 :=
  Quotient.mk (treeSetoid 3)
    ⟨SimpleGraph.pathGraph 3, by
      apply SimpleGraph.isTree_iff_connected_and_card.mpr
      constructor
      · simpa using (SimpleGraph.pathGraph_connected 2)
      · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        rw [← SimpleGraph.edgeFinset_card]
        simp [SimpleGraph.edgeFinset, path3_edgeSet]⟩

private noncomputable def p4Tree : UnlabelledTree 4 :=
  Quotient.mk (treeSetoid 4)
    ⟨SimpleGraph.pathGraph 4, by
      apply SimpleGraph.isTree_iff_connected_and_card.mpr
      constructor
      · simpa using (SimpleGraph.pathGraph_connected 3)
      · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        rw [← SimpleGraph.edgeFinset_card]
        simp [SimpleGraph.edgeFinset, path4_edgeSet]⟩

private noncomputable def k13Tree : UnlabelledTree 4 :=
  Quotient.mk (treeSetoid 4)
    ⟨SimpleGraph.starGraph (0 : Fin 4), SimpleGraph.isTree_starGraph _⟩

/-- Claim 5086: at redundancy two, the actual observability defect is the
intersection of the leaf-deck kernel and the three exact nonconstant motif
channels P₃, K_{1,3}, and P₄. -/
def explicitRedundancyTwoDefect : Prop :=
  ∀ n : ℕ,
    LinearMap.ker (observabilityMap n 2) =
      LinearMap.ker (leafDeck n) ⊓
        LinearMap.ker ((leafDeck n).comp (motifDiagonal p3Tree n)) ⊓
          LinearMap.ker ((leafDeck n).comp (motifDiagonal k13Tree n)) ⊓
            LinearMap.ker ((leafDeck n).comp (motifDiagonal p4Tree n))

end MathlibPlus.Combinatorics.Claim5086
