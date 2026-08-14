import Mathlib

namespace MathlibPlus.GraphTheory.Claim21230

/-- A finite graph with at least two connected components admits a nontrivial
partition of its components into two sides; every edge stays within one side.
The no-isolated-vertices hypothesis is retained from the source claim. -/
theorem exists_component_partition_claim21230
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (_h_no_isolated : ∀ v, ¬ G.IsIsolated v)
    (hcomponents : ∃ c d : G.ConnectedComponent, c ≠ d) :
    ∃ A B : Set V,
      A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Set.univ ∧
        ∀ ⦃u v : V⦄, G.Adj u v →
          (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) := by
  obtain ⟨c, d, hcd⟩ := hcomponents
  let A : Set V := c.supp
  let B : Set V := Aᶜ
  have hA : A.Nonempty := by
    exact c.nonempty_supp
  have hd : d.supp.Nonempty := d.nonempty_supp
  have hd_not_A : ∀ v ∈ d.supp, v ∉ A := by
    intro v hv hvc
    exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hvc hv)
  have hB : B.Nonempty := by
    obtain ⟨v, hv⟩ := hd
    refine ⟨v, ?_⟩
    change v ∉ A
    exact hd_not_A v hv
  have hdisjoint : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    intro v hvA hvB
    exact hvB hvA
  have hunion : A ∪ B = Set.univ := by
    ext v
    by_cases hv : v ∈ A <;> simp [B]
  refine ⟨A, B, hA, hB, hdisjoint, hunion, ?_⟩
  intro u v huv
  by_cases hu : u ∈ A
  · left
    refine ⟨hu, ?_⟩
    exact (c.mem_supp_congr_adj huv).mp hu
  · right
    refine ⟨?_, ?_⟩
    · change u ∉ A
      exact hu
    · change v ∉ A
      intro hv
      exact hu ((c.mem_supp_congr_adj huv).mpr hv)

end MathlibPlus.GraphTheory.Claim21230
