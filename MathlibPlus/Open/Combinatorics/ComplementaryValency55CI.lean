import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-!
Formalization of admitted claim 38208. The group is the additive product
`C₂³ × C₉`, represented by products of `ZMod`. A Cayley graph is represented
by its difference relation; graph isomorphism is an arbitrary permutation of
the vertex set preserving that relation, while the CI predicate asks for an
additive automorphism carrying one connection set to another. The source
claim does not restate the earlier valency-16 atlas theorem, so the valency-55
conclusion is recorded directly and the complement transfer is recorded
separately.
-/

def complementaryValency55CI : Prop :=
  let G := (ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9
  let base : Finset G := Finset.univ.erase (0 : G)
  let inverseClosed : Finset G → Prop := fun S =>
    ∀ x : G, x ∈ S ↔ -x ∈ S
  let complement : Finset G → Finset G := fun S => base \ S
  let cayleyIso : Finset G → Finset G → Prop := fun S T =>
    ∃ e : G ≃ G, ∀ x y : G,
      (x - y ∈ S ↔ e x - e y ∈ T)
  let ci : Finset G → Prop := fun S =>
    ∀ T : Finset G,
      inverseClosed T →
      (0 : G) ∉ T →
      cayleyIso S T →
      ∃ φ : G ≃+ G, Finset.image (φ : G → G) S = T
  let admissible : ℕ → Finset G → Prop := fun k S =>
    inverseClosed S ∧ (0 : G) ∉ S ∧ S.card = k
  Fintype.card G = 72 ∧
    (∀ S : Finset G,
      admissible 16 S →
        admissible 55 (complement S) ∧
        complement (complement S) = S ∧
        (ci S ↔ ci (complement S))) ∧
    (∀ S T : Finset G,
      (0 : G) ∉ S →
      (0 : G) ∉ T →
      (cayleyIso S T ↔ cayleyIso (complement S) (complement T))) ∧
    (∀ S : Finset G, admissible 55 S → ci S)

end MathlibPlus.Open.Combinatorics
