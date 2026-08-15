import Mathlib

namespace MathlibPlus.Open.CI

abbrev MixedAbelianC4C3Cubed : Type := ZMod 4 × (Fin 3 → ZMod 3)

/-- Negation of a subset of the additive group `MixedAbelianC4C3Cubed`. -/
def negSet (S : Set MixedAbelianC4C3Cubed) : Set MixedAbelianC4C3Cubed :=
  {x | -x ∈ S}

/-- The adjacency relation of the additive Cayley graph with connection set `S`. -/
def cayleyAdj (S : Set MixedAbelianC4C3Cubed)
    (x y : MixedAbelianC4C3Cubed) : Prop :=
  y - x ∈ S

/-- Isomorphism of the concrete Cayley adjacency relations on the common vertex group. -/
def cayleyGraphIso (S T : Set MixedAbelianC4C3Cubed) : Prop :=
  ∃ e : MixedAbelianC4C3Cubed ≃ MixedAbelianC4C3Cubed,
    ∀ x y,
      cayleyAdj S x y ↔ cayleyAdj T (e x) (e y)

/-- Every ordinary undirected Cayley graph on
`(Z/4Z) × F_3^3` of valency or covalency at most ten is CI. -/
def mixedAbelianC4C3CubedValencyTails : Prop :=
  ∀ (S T : Set MixedAbelianC4C3Cubed),
    S ⊆ (Set.univ : Set MixedAbelianC4C3Cubed) \ {0} →
    T ⊆ (Set.univ : Set MixedAbelianC4C3Cubed) \ {0} →
    S = negSet S →
    T = negSet T →
    cayleyGraphIso S T →
    Nat.min S.ncard (107 - S.ncard) ≤ 10 →
    ∃ α : MixedAbelianC4C3Cubed ≃+ MixedAbelianC4C3Cubed,
      α '' S = T

end MathlibPlus.Open.CI
