import Mathlib

namespace MathlibPlus.GraphTheory

/-- The leaf-set part of the pendant-attachment identity from claim 10154.
The finite-neighborhood carrier is the graph obtained by adjoining `none` and
joining it to `root`; the nontriviality hypothesis excludes the one-vertex
boundary case. -/
theorem leafSet_after_pendant_attachment_claim10154
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree)
    (hcard : 2 ≤ Fintype.card V) (root : V) :
    let neighbors : V → Finset V := fun v =>
      (G.neighborSet v).toFinite.toFinset
    let attachedNeighbors : Option V → Finset (Option V) := fun w =>
      match w with
      | none => {some root}
      | some v =>
          (neighbors v).image some ∪ if v = root then {none} else ∅
    {w | (attachedNeighbors w).card = 1} =
      {none} ∪ some '' ({v | (neighbors v).card = 1} \ {root}) := by
  classical
  let neighbors : V → Finset V := fun v =>
    (G.neighborSet v).toFinite.toFinset
  have hne : ∃ w : V, w ≠ root := by
    by_contra h
    push Not at h
    have hle : Fintype.card V ≤ 1 :=
      (Fintype.card_le_one_iff).2 (fun a b => (h a).trans (h b).symm)
    omega
  have hroot : (neighbors root).Nonempty := by
    obtain ⟨w, hw⟩ := hne
    obtain ⟨p⟩ := hG.connected.preconnected root w
    have hp : ¬p.Nil := p.not_nil_of_ne (Ne.symm hw)
    refine ⟨p.snd, ?_⟩
    exact (Set.Finite.mem_toFinset (G.neighborSet root).toFinite).mpr
      ((G.mem_neighborSet root p.snd).mpr (p.adj_snd hp))
  dsimp
  ext w
  cases w with
  | none => simp
  | some x =>
      by_cases hx : x = root
      · subst x
        have hnotiso : ¬G.IsIsolated root := by
          intro hiso
          rcases hroot with ⟨u, hu⟩
          exact hiso u ((G.mem_neighborSet root u).mp
            ((Set.Finite.mem_toFinset (G.neighborSet root).toFinite).mp hu))
        simp [hnotiso]
      · simp [hx, Finset.card_image_of_injective _ (Option.some_injective V)]

end MathlibPlus.GraphTheory
