import Mathlib

namespace MathlibPlus.Combinatorics.Claim30272

/-- A finite partition with a finer relation has no strictly finer quotient when
both quotient cardinalities agree. -/
theorem partitionRefinement_of_card_eq
    {α : Type*} [Fintype α]
    (aut graph : α → α → Prop)
    (haut : Equivalence aut)
    (hgraph : Equivalence graph)
    (hrefine : ∀ {a b : α}, aut a b → graph a b)
    [DecidableRel aut] [DecidableRel graph]
    (hcard : Fintype.card
        (Quotient ({ r := graph, iseqv := hgraph } : Setoid α)) =
      Fintype.card
        (Quotient ({ r := aut, iseqv := haut } : Setoid α))) :
    ∀ a b, graph a b ↔ aut a b := by
  let sa : Setoid α := ⟨aut, haut⟩
  let sg : Setoid α := ⟨graph, hgraph⟩
  let f : Quotient sa → Quotient sg :=
    Quotient.map id (by
      intro a b hab
      exact hrefine hab)
  have hf_surj : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ a =>
      refine ⟨Quotient.mk sa a, ?_⟩
      change Quotient.map id _ (Quotient.mk sa a) = Quotient.mk sg a
      rw [Quotient.map_mk]
      rfl
  have hf_bij : Function.Bijective f := by
    apply (Fintype.bijective_iff_surjective_and_card f).2
    refine ⟨hf_surj, ?_⟩
    simpa [sa, sg] using hcard.symm
  have hf_inj : Function.Injective f := hf_bij.1
  intro a b
  constructor
  · intro hab
    have hq : f (Quotient.mk sa a) = f (Quotient.mk sa b) := by
      change Quotient.map id _ (Quotient.mk sa a) =
        Quotient.map id _ (Quotient.mk sa b)
      rw [Quotient.map_mk, Quotient.map_mk]
      exact Quotient.sound hab
    have hq' : Quotient.mk sa a = Quotient.mk sa b := hf_inj hq
    exact Quotient.exact hq'
  · intro hab
    exact hrefine hab

end MathlibPlus.Combinatorics.Claim30272
