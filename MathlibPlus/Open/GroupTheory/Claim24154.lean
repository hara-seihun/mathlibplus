import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Faithful registry node for the ten signature-separated atlas types.  The
atlas predicates and complement relation remain explicit source interfaces;
Fin 5 × Bool records five groups with two complementary types each. -/
def signatureSeparatedFiniteTypes_claim24154
    (Atlas : Type*) [Fintype Atlas]
    (signatureSeparated : Atlas → Prop)
    (evenDihedral : Atlas → Prop)
    (indexTwoCompleteBipartite : Atlas → Prop)
    (complementPair : Atlas → Atlas → Prop) : Prop :=
  ∃ types : (Fin 5 × Bool) → Atlas,
    Function.Injective types ∧
    (∀ i : Fin 5,
      evenDihedral (types (i, false)) ∧
      evenDihedral (types (i, true)) ∧
      indexTwoCompleteBipartite (types (i, false)) ∧
      complementPair (types (i, false)) (types (i, true))) ∧
    (∀ x : Atlas,
      signatureSeparated x ↔ ∃ t : Fin 5 × Bool, x = types t)

end MathlibPlus.Open.GroupTheory
