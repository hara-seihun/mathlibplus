import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 28217: `A₄` is graph-CI and has exactly 22 unlabeled Cayley graphs.

The second conjunct counts inverse-closed, identity-free Cayley connection sets
up to graph isomorphism, so it counts the claimed unlabeled graphs rather than
labelled connection sets. -/
def alternatingFourGraphCIAndCount : Prop :=
  let G := alternatingGroup (Fin 4)
  let C := {S : Finset G // (1 : G) ∉ S ∧ ∀ x : G, x ∈ S → x⁻¹ ∈ S}
  letI : Setoid C :=
    { r := fun S T =>
        Nonempty (SimpleGraph.mulCayley (S.1 : Set G) ≃g
          SimpleGraph.mulCayley (T.1 : Set G))
      iseqv :=
        { refl := fun S => ⟨SimpleGraph.Iso.refl⟩
          symm := fun h => ⟨h.some.symm⟩
          trans := fun hST hTU => ⟨hTU.some.comp hST.some⟩ } }
  letI : Fintype (Quotient (inferInstance : Setoid C)) :=
    Fintype.ofFinite _
  (∀ S T : Set G,
      S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
        Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
          ∃ φ : G ≃* G, φ '' S = T) ∧
    Fintype.card (Quotient (inferInstance : Setoid C)) = 22

end MathlibPlus.Open.GraphTheory
