import MathlibPlus.Open.ResearchFormalization.R1416BlockClaims
import MathlibPlus.Open.ResearchFormalization.R1416Claim36966_36967
import MathlibPlus.Open.ResearchFormalization.R1416.NonregularBlockCriterionClaim36971

namespace MathlibPlus.Open.ResearchFormalization.R1416.Claim36969

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1416
open MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

/-- Claim 36969: the four exact subgroup rows for `H=C×U` in the coprime
product `A×(C₇:C₃)`, with their core, block-action quotient, and stabilizer
quotient carriers. -/
def claim36969 : Prop :=
  ∀ (A : Type*) [Fintype A] [CommGroup A],
    Nat.Coprime (Fintype.card A) 21 →
      letI : Fintype Frobenius21 := Fintype.ofFinite Frobenius21
      let G := A × Frobenius21
      ∀ (C : Subgroup A) (U : Subgroup Frobenius21)
        (H : Subgroup G),
        H = C.prod U →
          ((U = (⊥ : Subgroup Frobenius21) ∧
              coreOf H = C.prod (⊥ : Subgroup Frobenius21) ∧
              Nonempty
                (blockImageQuotient H ≃* (A ⧸ C) × Frobenius21) ∧
              Nat.card (blockStabilizerQuotient H) = 1) ∨
            (Nat.card U = 3 ∧
              coreOf H = C.prod (⊥ : Subgroup Frobenius21) ∧
              Nonempty
                (blockImageQuotient H ≃* (A ⧸ C) × Frobenius21) ∧
              Nonempty (blockStabilizerQuotient H ≃* C3)) ∨
            (Nat.card U = 7 ∧ U.Normal ∧
              coreOf H = C.prod U ∧
              Nonempty
                (blockImageQuotient H ≃* (A ⧸ C) × C3) ∧
              Nat.card (blockStabilizerQuotient H) = 1) ∨
            (U = (⊤ : Subgroup Frobenius21) ∧
              coreOf H = C.prod (⊤ : Subgroup Frobenius21) ∧
              Nonempty (blockImageQuotient H ≃* (A ⧸ C)) ∧
              Nat.card (blockStabilizerQuotient H) = 1))

end

end MathlibPlus.Open.ResearchFormalization.R1416.Claim36969
