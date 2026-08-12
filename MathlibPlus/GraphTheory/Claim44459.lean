import Mathlib.Combinatorics.SimpleGraph.Finite

namespace MathlibPlus.GraphTheory.Claim44459

/-!
Claim 44459.  The packet's `star(c)` is Mathlib's incidence set.  The
nonemptiness and distinct-vertex hypotheses are retained explicitly.
-/

/--
If the nonempty incidence set of `c` is contained in that of a distinct vertex
`z`, then `c` is a leaf.
-/
theorem degree_eq_one_of_incidenceSet_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {c z : V} (hcz : c ≠ z)
    (hc : (G.incidenceSet c).Nonempty)
    (hsub : G.incidenceSet c ⊆ G.incidenceSet z) :
    G.degree c = 1 := by
  have hcz_adj : G.Adj c z := by
    rcases hc with ⟨e, he⟩
    exact G.adj_of_mem_incidenceSet hcz he (hsub he)
  have hsingleton : G.incidenceSet c = {s(c, z)} := by
    calc
      G.incidenceSet c = G.incidenceSet c ∩ G.incidenceSet z :=
        (Set.inter_eq_left.mpr hsub).symm
      _ = {s(c, z)} := G.incidenceSet_inter_incidenceSet_of_adj hcz_adj
  calc
    G.degree c = Fintype.card (G.incidenceSet c) :=
      (G.card_incidenceSet_eq_degree c).symm
    _ = Fintype.card ({s(c, z)} : Set (Sym2 V)) :=
      Fintype.card_congr (Equiv.setCongr hsingleton)
    _ = 1 := by simp

end MathlibPlus.GraphTheory.Claim44459
