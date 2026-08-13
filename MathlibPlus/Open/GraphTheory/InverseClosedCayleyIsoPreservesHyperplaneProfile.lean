import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Any ordinary Cayley-graph transport between inverse-closed connection sets
on `𝔽₃^r` preserves the multiset of hyperplane-intersection counts. Thus the
hyperplane-profile mismatch branch of the inverse-pair component method is
impossible. -/
def inverseClosedCayleyIsoPreservesHyperplaneProfile : Prop :=
  ∀ (r : ℕ),
    let V := Fin r → ZMod 3
    ∀ (S T : Finset V) (q : V ≃ V),
      0 ∉ S →
      0 ∉ T →
      (∀ s : V, s ∈ S ↔ -s ∈ S) →
      (∀ t : V, t ∈ T ↔ -t ∈ T) →
      (∀ x y : V, y - x ∈ S ↔ q y - q x ∈ T) →
      ∃ σ : {a : V // a ≠ 0} ≃ {a : V // a ≠ 0},
        ∀ a,
          (S.filter fun s => (∑ i, a.1 i * s i) = 0).card =
            (T.filter fun t => (∑ i, (σ a).1 i * t i) = 0).card

end MathlibPlus.Open.GraphTheory
