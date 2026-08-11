import Mathlib

namespace MathlibPlus.Combinatorics

/-- A linear packing of 3-element subsets has vertex degree at most half of the
other vertices.  The hypotheses spell out the usual meaning of a linear
triangle packing on the finite vertex set `vertices`. -/
theorem vertexIncidenceCap_claim26090
    {α : Type*} [DecidableEq α]
    (vertices : Finset α) (triangles : Finset (Finset α))
    (htriangle : ∀ T ∈ triangles, T ⊆ vertices ∧ T.card = 3)
    (hlinear : ∀ {T U : Finset α}, T ∈ triangles → U ∈ triangles → T ≠ U →
      (T ∩ U).card ≤ 1) :
    ∀ v ∈ vertices,
      (triangles.filter (fun T => v ∈ T)).card ≤ (vertices.card - 1) / 2 := by
  intro v hv
  let incident : Finset (Finset α) := triangles.filter (fun T => v ∈ T)
  have hincident_subset : incident ⊆ triangles := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hincident_mem : ∀ T ∈ incident, v ∈ T := by
    intro T hT
    exact (Finset.mem_filter.mp hT).2
  have hpairwise : (incident : Set (Finset α)).PairwiseDisjoint (fun T => T.erase v) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro T hT U hU hinter
    by_contra hne
    have hTv : v ∈ T := hincident_mem T hT
    have hUv : v ∈ U := hincident_mem U hU
    obtain ⟨x, hx⟩ := hinter
    obtain ⟨hxT', hxU'⟩ := Finset.mem_inter.mp hx
    have hxT : x ∈ T := Finset.mem_of_mem_erase hxT'
    have hxU : x ∈ U := Finset.mem_of_mem_erase hxU'
    have hxne : x ≠ v := by
      exact (Finset.mem_erase.mp hxT').1
    have hpairs : ({v, x} : Finset α) ⊆ T ∩ U := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hTv, hUv⟩
      · exact Finset.mem_inter.mpr ⟨hxT, hxU⟩
    have hcard_inter : 2 ≤ (T ∩ U).card := by
      calc
        2 = ({v, x} : Finset α).card := by simp [Ne.symm hxne]
        _ ≤ (T ∩ U).card := Finset.card_le_card hpairs
    have hbad : 2 ≤ 1 := le_trans hcard_inter
      (hlinear (hincident_subset hT) (hincident_subset hU) hne)
    omega
  have hunion_subset : incident.biUnion (fun T => T.erase v) ⊆ vertices.erase v := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨T, hT, hxT⟩ := hx
    have hxT' : x ∈ T := Finset.mem_of_mem_erase hxT
    have hxv : x ≠ v := (Finset.mem_erase.mp hxT).1
    have hxvertices : x ∈ vertices := (htriangle T (hincident_subset hT)).1 hxT'
    exact Finset.mem_erase.mpr ⟨hxv, hxvertices⟩
  have hcard_each : ∀ T ∈ incident, (T.erase v).card = 2 := by
    intro T hT
    calc
      (T.erase v).card = T.card - 1 :=
        Finset.card_erase_of_mem (hincident_mem T hT)
      _ = 2 := by simp [((htriangle T (hincident_subset hT)).2)]
  have hunion_card : (incident.biUnion (fun T => T.erase v)).card = incident.card * 2 := by
    rw [Finset.card_biUnion hpairwise]
    calc
      (∑ u ∈ incident, (u.erase v).card) = ∑ u ∈ incident, 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hcard_each u hu
      _ = incident.card * 2 := by simp
  have hcard : incident.card * 2 ≤ vertices.card - 1 := by
    calc
      incident.card * 2 = (incident.biUnion (fun T => T.erase v)).card := hunion_card.symm
      _ ≤ (vertices.erase v).card := Finset.card_le_card hunion_subset
      _ = vertices.card - 1 := Finset.card_erase_of_mem hv
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hcard

end MathlibPlus.Combinatorics
