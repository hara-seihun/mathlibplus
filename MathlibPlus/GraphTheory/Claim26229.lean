import Mathlib

namespace MathlibPlus.GraphTheory

/--
Claim 26229.  In a finite vertex-transitive host, a two-vertex deletion is
isomorphic to the deletion of one further vertex from a fixed vertex-deleted
card.  The target is written as the equivalent induced graph on the two
remaining-vertex conditions.
-/
theorem twoCardsOfVertexTransitiveHost_claim26229
    (V : Type*) [Fintype V] (H : SimpleGraph V)
    (hvt : ∀ u v : V, ∃ e : H ≃g H, e u = v)
    (v u w : V) (huw : u ≠ w) :
    ∃ w' : {x : V // x ≠ v},
      Nonempty
        (H.induce {x : V | x ≠ u ∧ x ≠ w} ≃g
          H.induce {x : V | x ≠ v ∧ x ≠ (w' : V)}) := by
  obtain ⟨e, he⟩ := hvt u v
  have hew : e w ≠ v := by
    intro h
    apply huw
    exact e.injective (h.trans he.symm).symm
  let w' : {x : V // x ≠ v} := ⟨e w, hew⟩
  refine ⟨w', ⟨e.induce ?_⟩⟩
  apply e.bijOn
  intro x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxv, hxw⟩
    constructor
    · intro hxu
      exact hxv (hxu ▸ he)
    · intro hxw'
      apply hxw
      simpa [w'] using congrArg e hxw'
  · rintro ⟨hxu, hxw⟩
    constructor
    · intro hxe
      apply hxu
      exact e.injective (hxe.trans he.symm)
    · intro hxe
      apply hxw
      apply e.injective
      simpa [w'] using hxe

end MathlibPlus.GraphTheory
