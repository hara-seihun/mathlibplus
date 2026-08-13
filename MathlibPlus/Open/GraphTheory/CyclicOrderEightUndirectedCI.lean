import MathlibPlus.Basic

namespace MathlibPlus.Open.GraphTheory

/--
Claim 14570.  The ordinary undirected CI property for the cyclic group of
order eight, represented additively by `ZMod 8`.  Connection sets are
identity-free and inverse-closed; `cayleyIso` is the right-difference Cayley
relation, and `mapsByAut` requires an additive group automorphism carrying the
source set to the target set.
-/
def cyclicOrderEightUndirectedCI_claim14570 : Prop :=
  let isConnection : Set (ZMod 8) → Prop := fun S ↦
    0 ∉ S ∧ ∀ x ∈ S, -x ∈ S
  let cayleyIso : Set (ZMod 8) → Set (ZMod 8) → Prop := fun S T ↦
    ∃ e : ZMod 8 ≃ ZMod 8, ∀ x y : ZMod 8,
      (y - x ∈ S ↔ e y - e x ∈ T)
  let mapsByAut : Set (ZMod 8) → Set (ZMod 8) → Prop := fun S T ↦
    ∃ e : ZMod 8 ≃+ ZMod 8, Set.image e S = T
  ∀ S T, isConnection S → isConnection T → cayleyIso S T → mapsByAut S T

end MathlibPlus.Open.GraphTheory
