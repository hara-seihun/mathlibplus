import Mathlib.Combinatorics.SimpleGraph.Finite

open scoped Sym2
open SimpleGraph

namespace MathlibPlus.GraphTheory

/-- Claim 14310: if the incident-edge star at `c` is contained in the one at a
vertex `z ≠ c` in a finite simple graph with no isolated vertices, then `c`
has degree one. -/
theorem starSubsetForcesDegreeOne_claim14310
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c z : V)
    (h_no_isolated : ∀ v, ¬ G.IsIsolated v)
    (hcz : c ≠ z)
    (hstar : G.incidenceSet c ⊆ G.incidenceSet z) :
    let _ : Fintype (G.neighborSet c) := Fintype.ofFinite _
    G.degree c = 1 := by
  let _ : Fintype (G.neighborSet c) := Fintype.ofFinite _
  have hcpos : 0 < G.degree c := (G.degree_pos c).2 (h_no_isolated c)
  have hnon : (G.incidenceSet c).Nonempty := by
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_nonempty).mp hcpos
    exact ⟨s(c, w), G.mk'_mem_incidenceSet_left_iff.mpr hw⟩
  have hneigh : G.neighborSet c = {z} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · obtain ⟨e, he⟩ := hnon
      have hez : e ∈ G.incidenceSet z := hstar he
      have hczadj := G.adj_of_mem_incidenceSet hcz he hez
      exact (G.mem_neighborSet c z).mpr hczadj
    · intro w hw
      have he : s(c, w) ∈ G.incidenceSet c := G.mem_incidence_iff_neighbor.mpr hw
      have hez : s(c, w) ∈ G.incidenceSet z := hstar he
      rcases (G.mk'_mem_incidenceSet_iff).mp hez with ⟨_, hzc | hzw⟩
      · exact (hcz hzc.symm).elim
      · exact hzw.symm
  have hcard : Fintype.card (G.neighborSet c) = 1 := by
    calc
      Fintype.card (G.neighborSet c) = Fintype.card ({z} : Set V) :=
        Fintype.card_congr (Equiv.setCongr hneigh)
      _ = 1 := by simp
  calc
    G.degree c = Fintype.card (G.neighborSet c) := (G.card_neighborSet_eq_degree c).symm
    _ = 1 := hcard

end MathlibPlus.GraphTheory
