import MathlibPlus.Open.GraphTheory.FiniteCIBatch

namespace MathlibPlus.Open.ResearchFormalization.Claim61136C3Q8

noncomputable section

abbrev C3Q8 :=
  MathlibPlus.Open.GraphTheory.FiniteCIBatch.cyclicGroup 3 × QuaternionGroup 2

def identityFreeInverseClosed (S : Set C3Q8) : Prop :=
  (1 : C3Q8) ∉ S ∧ ∀ x : C3Q8, x ∈ S ↔ x⁻¹ ∈ S

def simultaneousCayleyIsomorphism
    {I : Type*} (S T : I → Set C3Q8) (e : C3Q8 ≃ C3Q8) : Prop :=
  ∀ i : I, ∀ x y : C3Q8,
    x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i

/-- Claim 61136: one vertex bijection simultaneously isomorphing an arbitrary
finite labelled tuple of symmetric Cayley relations on `C₃ × Q₈` is induced
on every connection set by one group automorphism. -/
def c3Q8FiniteLabelledTupleCI_claim61136 : Prop :=
  ∀ (I : Type*) [Fintype I]
    (S T : I → Set C3Q8)
    (hS : ∀ i : I, identityFreeInverseClosed (S i))
    (hT : ∀ i : I, identityFreeInverseClosed (T i))
    (e : C3Q8 ≃ C3Q8),
    simultaneousCayleyIsomorphism S T e →
      ∃ α : C3Q8 ≃* C3Q8, ∀ i : I, α '' S i = T i

end

end MathlibPlus.Open.ResearchFormalization.Claim61136C3Q8
