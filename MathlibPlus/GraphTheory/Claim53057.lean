import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace MathlibPlus.GraphTheory.Claim53057

open scoped Pointwise

/-- In the product Cayley graph, adjacency is exactly inequality of the first
coordinate.  The finite nontrivial group hypotheses mirror the claim. -/
theorem adj_iff_first_coordinate_ne_claim53057
    {A H : Type*} [Group A] [Group H] [Fintype A] [Fintype H]
    [Nontrivial A] [Nontrivial H] (a a' : A) (h h' : H) :
    (SimpleGraph.mulCayley
      ((Set.univ \ ({1} : Set A)) ×ˢ (Set.univ : Set H))).Adj (a, h) (a', h') ↔
      a ≠ a' := by
  rw [SimpleGraph.mulCayley_adj]
  simp only [Set.mem_prod, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
    Prod.inv_mk, Prod.mk_mul_mk]
  simp only [true_and, and_true]
  change ((a, h) ≠ (a', h') ∧
      (a⁻¹ * a' ≠ 1 ∨ a'⁻¹ * a ≠ 1)) ↔ a ≠ a'
  constructor
  · rintro ⟨_, ha | ha⟩ haa
    · exact ha (by simp [haa])
    · exact ha (by simp [haa])
  · intro haa
    refine ⟨?_, ?_⟩
    · intro hEq
      exact haa (congrArg Prod.fst hEq)
    · left
      intro hEq
      exact haa (eq_of_inv_mul_eq_one hEq)


/-- The displayed connection set is inverse-closed. -/
theorem connectionSet_inv_closed_claim53057
    {A H : Type*} [Group A] [Group H] [Fintype A] [Fintype H]
    [Nontrivial A] [Nontrivial H] :
    (((Set.univ \ ({1} : Set A)) ×ˢ (Set.univ : Set H)) : Set (A × H))⁻¹ =
      (Set.univ \ ({1} : Set A)) ×ˢ (Set.univ : Set H) := by
  ext x
  simp [Set.mem_prod]

/-- Non-adjacency is the equivalence relation of having the same first
coordinate, so the graph is complete multipartite. -/
theorem isCompleteMultipartite_product_cayley_claim53057
    {A H : Type*} [Group A] [Group H] [Fintype A] [Fintype H] [Nontrivial A]
    [Nontrivial H] :
    (SimpleGraph.mulCayley
      ((Set.univ \ ({1} : Set A)) ×ˢ (Set.univ : Set H))).IsCompleteMultipartite := by
  constructor
  intro x y z hxy hyz
  have hxy' : x.1 = y.1 := by
    by_contra hne
    exact hxy ((adj_iff_first_coordinate_ne_claim53057 x.1 y.1 x.2 y.2).2 hne)
  have hyz' : y.1 = z.1 := by
    by_contra hne
    exact hyz ((adj_iff_first_coordinate_ne_claim53057 y.1 z.1 y.2 z.2).2 hne)
  intro hxz
  have hxz' : x.1 ≠ z.1 :=
    (adj_iff_first_coordinate_ne_claim53057 x.1 z.1 x.2 z.2).1 hxz
  exact hxz' (hxy'.trans hyz')


/-- Nontriviality of the first factor gives a two-step path within each
first-coordinate fibre, and one edge between distinct fibres. -/
theorem connected_product_cayley_claim53057
    {A H : Type*} [Group A] [Group H] [Fintype A] [Fintype H]
    [Nontrivial A] [Nontrivial H] :
    (SimpleGraph.mulCayley
      ((Set.univ \ ({1} : Set A)) ×ˢ (Set.univ : Set H))).Connected := by
  let G : SimpleGraph (A × H) := SimpleGraph.mulCayley
    ((Set.univ \ ({1} : Set A)) ×ˢ (Set.univ : Set H))
  apply (G.connected_iff_exists_forall_reachable).2
  refine ⟨(1, 1), ?_⟩
  intro w
  by_cases ha : (1 : A) = w.1
  · obtain ⟨b, hb⟩ := exists_ne (1 : A)
    have hleft : G.Adj (1, 1) (b, 1) := by
      apply (adj_iff_first_coordinate_ne_claim53057 (1 : A) b (1 : H) (1 : H)).2
      exact hb.symm
    have hright : G.Adj (b, 1) w := by
      apply (adj_iff_first_coordinate_ne_claim53057 b w.1 (1 : H) w.2).2
      simpa [ha] using hb
    exact hleft.reachable.trans hright.reachable
  · exact (adj_iff_first_coordinate_ne_claim53057 (1 : A) w.1 (1 : H) w.2).2 ha |>.reachable

end MathlibPlus.GraphTheory.Claim53057
