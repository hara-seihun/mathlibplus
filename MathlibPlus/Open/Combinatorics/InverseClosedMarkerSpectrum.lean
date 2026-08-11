import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Group.InjSurj

namespace MathlibPlus.Open.Combinatorics

/-- Claim 53532: every finite group has an inverse-closed subset of each
cardinality from zero through its cardinality.  The statement records
existence only; it does not choose a canonical subset for each size. -/
def inverseClosedMarkerSpectrum : Prop :=
  ∀ (G : Type*) [Group G] [Finite G] (n : ℕ),
    n ≤ Nat.card G →
      ∃ S : Finset G,
        (∀ x : G, x ∈ S ↔ x⁻¹ ∈ S) ∧ S.card = n

end MathlibPlus.Open.Combinatorics
