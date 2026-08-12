import MathlibPlus.Basic

open SimpleGraph

namespace MathlibPlus.Combinatorics.Claim20574

/-- A spanning tree on the four labeled vertices has exactly three edges. -/
theorem spanningTree_card (T : SimpleGraph (Fin 4)) (hT : T.IsTree) :
    Nat.card T.edgeSet = 3 := by
  classical
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  have h := hT.card_edgeFinset
  simp only [Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card, ← T.edgeFinset_card]
  omega

/-- For a finite edge set `K`, deleting one labeled edge leaves a containing
three-edge set `T` exactly when that edge was not already in `T`. -/
theorem deleteOne_contains_iff {α : Type*} [DecidableEq α] (K T : Finset α)
    (hTK : T ⊆ K) (f : α) :
    T ⊆ K.erase f ↔ f ∉ T := by
  classical
  constructor
  · intro h hf
    have hff : f ∈ K.erase f := h hf
    simp at hff
  · intro hf x hx
    have hxK : x ∈ K := hTK hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, hxK⟩
    intro hxf
    exact hf (hxf ▸ hx)

/-- A three-edge spanning tree in a six-edge complete graph has three
excluded edges. -/
theorem three_excluded {α : Type*} [DecidableEq α] (K T : Finset α)
    (hTK : T ⊆ K) (hK : K.card = 6) (hT : T.card = 3) :
    (K \ T).card = 3 := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTK, hK, hT]

/-- The three missing edges are exactly the three labeled diamonds that
contain the tree. -/
theorem diamond_count {α : Type*} [DecidableEq α] (K T : Finset α)
    (hTK : T ⊆ K) (hK : K.card = 6) (hT : T.card = 3) :
    (K.filter (fun f => T ⊆ K.erase f)).card = 3 := by
  classical
  have hfilter : K.filter (fun f => T ⊆ K.erase f) = K \ T := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    rw [deleteOne_contains_iff K T hTK f]
  rw [hfilter]
  exact three_excluded K T hTK hK hT

end MathlibPlus.Combinatorics.Claim20574
