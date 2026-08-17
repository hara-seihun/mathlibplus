import MathlibPlus.Open.ResearchFormalization.R1416BlockClaims

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1416

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

/-- The kernel of the left regular action on the blocks through a subgroup. -/
def regularBlockKernelSet {G : Type*} [Group G]
    (H : Subgroup G) : Set G :=
  {g | ∀ x : G, regularBlock H (g * x) = regularBlock H x}

/-- Exact core and regularity criterion for every coprime product block row. -/
def exactNonregularBlockActionCriterion_claim36971 : Prop :=
  ∀ (A : Type*) [Fintype A] [CommGroup A],
    Nat.Coprime (Fintype.card A) 21 →
      letI : Fintype Frobenius21 := Fintype.ofFinite Frobenius21
      let G := A × Frobenius21
      ∀ (C : Subgroup A) (U : Subgroup Frobenius21)
        (H : Subgroup G),
        H = C.prod U →
          regularBlockKernelSet H = (coreOf H : Set G) ∧
            (blockActionRegular H ↔ Nat.card U ≠ 3) ∧
            (Nat.card U = 3 →
              Nat.card (blockStabilizerQuotient H) = 3)

end

end MathlibPlus.Open.ResearchFormalization.R1416
