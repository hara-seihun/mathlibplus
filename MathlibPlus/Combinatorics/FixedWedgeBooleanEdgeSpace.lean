import Mathlib.Combinatorics.SimpleGraph.Basic

open scoped Sym2

namespace MathlibPlus.Combinatorics

/-- Claim 21559: after deleting the two wedge edges `xu` and `xv` from the
complete edge set, every remaining edge belongs either to the edge cube on
`V \ {u,v}` or to the edge cube on `V \ {x}`. The source does not require an
additional graph structure, so the two embedded cubes are represented by the
edge sets of the corresponding symmetric `fromRel` graphs. -/
theorem fixedWedgeBooleanEdgeSpaceCover
    {V : Type*} [DecidableEq V]
    (x u v : V) (hxu : x ≠ u) (hxv : x ≠ v) (_huv : u ≠ v) :
    let W : Set (Sym2 V) :=
      (⊤ : SimpleGraph V).edgeSet \ {s(x, u), s(x, v)}
    let U : Set (Sym2 V) :=
      (SimpleGraph.fromRel (fun a b : V =>
        a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v)).edgeSet
    let Vcube : Set (Sym2 V) :=
      (SimpleGraph.fromRel (fun a b : V => a ≠ x ∧ b ≠ x)).edgeSet
    W ⊆ U ∪ Vcube := by
  dsimp
  intro e he
  rcases he with ⟨heW, hnot⟩
  revert heW hnot
  refine Sym2.inductionOn e ?_
  intro a b heW hnot
  have hab : a ≠ b := by
    simpa only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] using heW
  simp only [Set.mem_union]
  by_cases hax : a = x
  · subst a
    have hbu : b ≠ u := by
      intro h
      apply hnot
      simp [h]
    have hbv : b ≠ v := by
      intro h
      apply hnot
      simp [h]
    left
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
    exact ⟨hab, Or.inl ⟨hxu, hxv, hbu, hbv⟩⟩
  · by_cases hbx : b = x
    · subst b
      have hau : a ≠ u := by
        intro h
        apply hnot
        have heq : s(a, x) = s(x, u) :=
          (Sym2.eq_iff).2 (Or.inr ⟨h, rfl⟩)
        simp [heq]
      have hav : a ≠ v := by
        intro h
        apply hnot
        have heq : s(a, x) = s(x, v) :=
          (Sym2.eq_iff).2 (Or.inr ⟨h, rfl⟩)
        simp [heq]
      left
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
      exact ⟨hab, Or.inr ⟨hxu, hxv, hau, hav⟩⟩
    · right
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
      exact ⟨hab, Or.inl ⟨hax, hbx⟩⟩

end MathlibPlus.Combinatorics
