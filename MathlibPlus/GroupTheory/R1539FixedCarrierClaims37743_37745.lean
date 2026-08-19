import MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745

open Classical

namespace MathlibPlus.GroupTheory.R1539FixedCarrier

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745

abbrev C5A4Omega := Omega
abbrev C5A4H := H
abbrev C5A4K := K
abbrev C5A4Generated := generatedX

def translationSubgroup : Subgroup (Equiv.Perm C5A4Omega) :=
  Subgroup.closure cFactor

def regularPermutationSubgroup
    (L : Subgroup (Equiv.Perm C5A4Omega)) : Prop :=
  ∀ x y : C5A4Omega, ∃! h : L, h.1 x = y

/-- Claim 37743 with the cyclic factor represented by the additive cyclic
coordinate `Multiplicative (ZMod 5)`. -/
def claim37743_additive : Prop :=
  regularPermutationSubgroup C5A4H ∧
    regularPermutationSubgroup C5A4K ∧
    Nonempty (C5A4H ≃* (Multiplicative (ZMod 5) × A4)) ∧
    Nonempty (C5A4K ≃* (Multiplicative (ZMod 5) × A4)) ∧
    C5A4H ⊓ C5A4K = translationSubgroup

/-- Claim 37745 with the additive cyclic factor made explicit in both product
isomorphisms. -/
def claim37745_additive : Prop :=
  Nonempty (C5A4Generated ≃*
      (Multiplicative (ZMod 5) × A4 × A4)) ∧
    Nat.card C5A4Generated = 720 ∧
    (∀ x y : C5A4Omega, ∃ g : C5A4Generated, g.1 x = y)

end

end MathlibPlus.GroupTheory.R1539FixedCarrier
