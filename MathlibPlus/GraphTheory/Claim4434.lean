import Mathlib

namespace MathlibPlus.GraphTheory.Claim4434

open Sym2

/-- A vertex permutation acts on unordered pairs with distinct endpoints, and
its inverse acts by the inverse permutation. -/
theorem inducedEquivalenceOnSimpleEdges_claim4434 :
    ∀ (V : Type*) (σ : Equiv.Perm V),
      let E := {e : Sym2 V // ∃ x y : V, x ≠ y ∧ e = s(x, y)}
      ∃ f : E ≃ E,
        (∀ e : E, (f e).1 = Sym2.map σ e.1) ∧
        (∀ e : E, (f.symm e).1 = Sym2.map σ.symm e.1) := by
  intro V σ
  let E := {e : Sym2 V // ∃ x y : V, x ≠ y ∧ e = s(x, y)}
  let f : E → E := fun e => ⟨Sym2.map σ e.1, by
    rcases e.2 with ⟨x, y, hxy, he⟩
    refine ⟨σ x, σ y, σ.injective.ne hxy, ?_⟩
    rw [he, Sym2.map_mk]
  ⟩
  let g : E → E := fun e => ⟨Sym2.map σ.symm e.1, by
    rcases e.2 with ⟨x, y, hxy, he⟩
    refine ⟨σ.symm x, σ.symm y, σ.symm.injective.ne hxy, ?_⟩
    rw [he, Sym2.map_mk]
  ⟩
  have hfg : Function.LeftInverse g f := by
    intro e
    dsimp [f, g]
    apply Subtype.ext
    change Sym2.map σ.symm (Sym2.map σ e.1) = e.1
    rw [Sym2.map_map]
    simp
  have hgf : Function.LeftInverse f g := by
    intro e
    dsimp [f, g]
    apply Subtype.ext
    change Sym2.map σ (Sym2.map σ.symm e.1) = e.1
    rw [Sym2.map_map]
    simp
  have hf : Function.Bijective f := ⟨hfg.injective, hgf.surjective⟩
  let F : E ≃ E := Equiv.ofBijective f hf
  refine ⟨F, ?_, ?_⟩
  · intro e
    exact rfl
  · intro e
    have hsymm : F.symm e = g e := by
      apply (Equiv.symm_apply_eq F).2
      rw [Equiv.ofBijective_apply]
      exact (hgf e).symm
    exact congrArg Subtype.val hsymm

end MathlibPlus.GraphTheory.Claim4434
