import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory.Claim48810

/-- Switching a maximum cut cannot turn more monochromatic crossing-cut edges
into crossing edges than it turns crossing edges into monochromatic ones.  This
is the common cut-dominance core of admitted claims 48810 and 50201.  The edge
set is abstract so triangle-freeness and the codegree-zero demand set remain
outside this local lemma. -/
theorem maximumCutCutDominance_claim48810
    {Vertex Edge : Type*} [DecidableEq Vertex] [DecidableEq Edge]
    (edges : Finset Edge) (part : Vertex → Bool)
    (src dst : Edge → Vertex)
    (hmax : ∀ S : Finset Vertex,
      (edges.filter (fun e =>
        (if src e ∈ S then !(part (src e)) else part (src e)) ≠
          (if dst e ∈ S then !(part (dst e)) else part (dst e)))).card ≤
        (edges.filter (fun e => part (src e) ≠ part (dst e))).card) :
    ∀ S : Finset Vertex,
      (edges.filter (fun e =>
        part (src e) = part (dst e) ∧
          ((src e ∈ S) ≠ (dst e ∈ S)))).card ≤
      (edges.filter (fun e =>
        part (src e) ≠ part (dst e) ∧
          ((src e ∈ S) ≠ (dst e ∈ S)))).card := by
  classical
  intro S
  let B : Finset Edge := edges.filter (fun e => part (src e) ≠ part (dst e))
  let M : Finset Edge := edges.filter (fun e => part (src e) = part (dst e))
  let D : Finset Edge := edges.filter (fun e => (src e ∈ S) ≠ (dst e ∈ S))
  let BΔ : Finset Edge := B ∩ D
  let MΔ : Finset Edge := M ∩ D
  let switched : Finset Edge := edges.filter (fun e =>
    (if src e ∈ S then !(part (src e)) else part (src e)) ≠
      (if dst e ∈ S then !(part (dst e)) else part (dst e)))
  have hsw : switched = (B \ D) ∪ MΔ := by
    ext e
    by_cases he : e ∈ edges <;>
      by_cases hsrc : src e ∈ S <;>
      by_cases hdst : dst e ∈ S <;>
      by_cases hpart : part (src e) = part (dst e) <;>
      simp [switched, B, M, D, MΔ, he, hsrc, hdst, hpart]
  have hdisj : Disjoint (B \ D) MΔ := by
    rw [Finset.disjoint_left]
    intro e heB heM
    exact (Finset.mem_sdiff.mp heB).2 (Finset.mem_inter.mp heM).2
  have hcard_split : B.card = (B \ D).card + BΔ.card := by
    calc
      B.card = (B \ D ∪ B ∩ D).card := by rw [Finset.sdiff_union_inter]
      _ = (B \ D).card + (B ∩ D).card := by
        rw [Finset.card_union_of_disjoint]
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact (Finset.mem_sdiff.mp he1).2 (Finset.mem_inter.mp he2).2
      _ = (B \ D).card + BΔ.card := by rfl
  have hswitch_card : switched.card ≤ B.card := by
    exact hmax S
  rw [hsw, Finset.card_union_of_disjoint hdisj] at hswitch_card
  have hM : MΔ = edges.filter (fun e =>
      part (src e) = part (dst e) ∧ ((src e ∈ S) ≠ (dst e ∈ S))) := by
    ext e
    simp [MΔ, M, D, and_assoc, and_left_comm, and_comm]
  have hB : BΔ = edges.filter (fun e =>
      part (src e) ≠ part (dst e) ∧ ((src e ∈ S) ≠ (dst e ∈ S))) := by
    ext e
    simp [BΔ, B, D, and_assoc, and_left_comm, and_comm]
  have : MΔ.card ≤ BΔ.card := by omega
  simpa only [hM, hB] using this

end MathlibPlus.GraphTheory.Claim48810
