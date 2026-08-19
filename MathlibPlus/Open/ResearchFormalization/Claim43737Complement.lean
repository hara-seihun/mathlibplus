import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim43737

noncomputable section

/-- The exact nonidentity complement on a group of order ninety, including
valency reversal and distinct-record custody. -/
def inverseClosedComplement_claim43737 : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G],
    Fintype.card G = 90 →
    ∀ (S : Set G),
      S ⊆ (Set.univ : Set G) \ {1} →
      (∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S) →
        let complement : Set G :=
          ((Set.univ : Set G) \ {1}) \ S
        complement ⊆ (Set.univ : Set G) \ {1} ∧
          (∀ ⦃x : G⦄, x ∈ complement → x⁻¹ ∈ complement) ∧
          Set.ncard complement = 89 - Set.ncard S ∧
          S ≠ complement ∧
          ((89 : ℕ) - 35 = 54) ∧
          ((89 : ℕ) - 36 = 53) ∧
          ((89 : ℕ) - 37 = 52) ∧
          ((89 : ℕ) - 38 = 51) ∧
          ((89 : ℕ) - 39 = 50) ∧
          ((89 : ℕ) - 40 = 49) ∧
          ((89 : ℕ) - 41 = 48)

end

end MathlibPlus.Open.ResearchFormalization.Claim43737
