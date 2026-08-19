import Mathlib

namespace MathlibPlus.Open.Combinatorics.R1055

/-- Claim 28547: fixed-point-free involutive collision pairing forces a finite
invariant support to have even cardinality, so an odd nonempty support cannot
be invariant. -/
def oddSupportCannotBeInvariant_claim28547 : Prop :=
  ∀ (α : Type*) (K : Finset α) (θ : α → α),
    Function.Involutive θ →
    (∀ x, θ x ≠ x) →
    ((∀ x, x ∈ K → θ x ∈ K) → Even K.card) ∧
      (Odd K.card → K.Nonempty →
        ¬(∀ x, x ∈ K → θ x ∈ K))

end MathlibPlus.Open.Combinatorics.R1055
