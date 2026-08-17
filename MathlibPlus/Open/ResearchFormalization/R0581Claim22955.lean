import MathlibPlus.Open.FormalizationBatchUnionFamilies

namespace MathlibPlus.Open.ResearchFormalization.R0581Claim22955

open scoped BigOperators
open MathlibPlus.Open.FormalizationBatchUnionFamilies

noncomputable section

/-- The three minimum blocks used by the exact `1+10+10` fixture. -/
def counterexampleMinimum : Fin 3 → Finset CounterexampleGround :=
  ![counterexampleM₁, counterexampleM₂, counterexampleM₃]

/-- The equal-block normalized incidence of one member of the fixture. -/
def normalizedBlockIncidence
    (S : Finset CounterexampleGround) (i : Fin 3) : ℚ :=
  ((S ∩ counterexampleMinimum i).card : ℚ) /
    (counterexampleMinimum i).card

/-- The equal-block charge `2∑ |S∩M_i|/|M_i| - 3`. -/
def normalizedBlockCharge (S : Finset CounterexampleGround) : ℚ :=
  2 * (∑ i : Fin 3, normalizedBlockIncidence S i) - 3

/-- The total normalized incidence of the explicit 89-member family. -/
def normalizedIncidence89 : ℚ :=
  ∑ S ∈ exactOneTenTenFamily,
    ∑ i : Fin 3, normalizedBlockIncidence S i

/-- The total equal-block normalized charge of the explicit family. -/
def normalizedCharge89 : ℚ :=
  ∑ S ∈ exactOneTenTenFamily, normalizedBlockCharge S

/-- The number of members containing a coordinate of the explicit fixture. -/
def coordinateFrequency22955 (c : CounterexampleGround) : ℕ :=
  (exactOneTenTenFamily.filter (fun S => c ∈ S)).card

/-- Abundance means strictly more than half of the 89 family members. -/
def stronglyAbundant22955 (c : CounterexampleGround) : Prop :=
  (89 : ℚ) / 2 < (coordinateFrequency22955 c : ℚ)

/-- Claim 22955: the explicit 89-set fixture has negative total equal-block
    charge while its singleton, active ten-block, and outside coordinates are
    all strongly abundant. -/
def negativeNormalizedChargeButStrongAbundance_claim22955 : Prop :=
  exactOneTenTenCounterexampleClaim22954 ∧
    exactOneTenTenFamily.card = 89 ∧
    normalizedIncidence89 = 663 / 5 ∧
    normalizedCharge89 =
      2 * normalizedIncidence89 - 3 * (exactOneTenTenFamily.card : ℚ) ∧
    2 * normalizedIncidence89 - 3 * (exactOneTenTenFamily.card : ℚ) =
      -(9 : ℚ) / 5 ∧
    normalizedCharge89 = -(9 : ℚ) / 5 ∧
    normalizedCharge89 < 0 ∧
    coordinateFrequency22955 (0 : CounterexampleGround) = 85 ∧
    (∀ c : CounterexampleGround, c ∈ counterexampleD₂ →
      coordinateFrequency22955 c = 49) ∧
    (∀ c : CounterexampleGround, c ∈ counterexampleD₃ →
      coordinateFrequency22955 c = 49) ∧
    coordinateFrequency22955 (30 : CounterexampleGround) = 81 ∧
    stronglyAbundant22955 (0 : CounterexampleGround) ∧
    (∀ c : CounterexampleGround, c ∈ counterexampleD₂ →
      stronglyAbundant22955 c) ∧
    (∀ c : CounterexampleGround, c ∈ counterexampleD₃ →
      stronglyAbundant22955 c) ∧
    stronglyAbundant22955 (30 : CounterexampleGround)

end

end MathlibPlus.Open.ResearchFormalization.R0581Claim22955
