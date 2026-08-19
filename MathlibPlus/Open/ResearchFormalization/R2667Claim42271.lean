import MathlibPlus.Open.Combinatorics.R2667.Claim42272

namespace MathlibPlus.Open.ResearchFormalization.R2667Claim42271

open MathlibPlus.Open.Combinatorics.R2667.Claim42272
open scoped BigOperators

abbrev Ground14 := Fin 14
abbrev Family14 := MathlibPlus.Open.Combinatorics.UnionClosedBatch.Family 14

private def omissionCount14
    (B : Family14) (J Z : Finset Ground14) (y : Ground14) : ℕ :=
  traceCount14 B J Z - traceCoordinateCount14 B J Z y

private def totalOmissions14
    (B : Family14) (J : Finset Ground14) (y : Ground14) : ℕ :=
  ∑ Z ∈ occupiedTraces14 B J, omissionCount14 B J Z y

private def topReturnFamily14
    (B : Family14) (J : Finset Ground14) : Family14 :=
  B.image (fun A => A ∪ J)

private def fiberPartition14
    (B : Family14) (J : Finset Ground14) : Prop :=
  ∀ ⦃A : Finset Ground14⦄, A ∈ B →
    A ∈ traceFiber14 B J (outsideTrace14 A J) ∧
      outsideTrace14 A J ∈ occupiedTraces14 B J

private def topReturnAlignment14
    (G B : Family14) (R₁ R₂ J : Finset Ground14) : Prop :=
  (topReturnFamily14 B J).card = (occupiedTraces14 B J).card ∧
    (∀ Z ∈ occupiedTraces14 B J,
      Z ∪ J ∈ rootUpperFamily14 G R₁ ∧
        Z ∪ J ∈ rootUpperFamily14 G R₂) ∧
    (∀ ⦃A A' : Finset Ground14⦄, A ∈ B → A' ∈ B →
      (A ∪ J = A' ∪ J ↔
        outsideTrace14 A J = outsideTrace14 A' J))

private def topReturnResidual14
    (B : Family14) (J : Finset Ground14) (y : Ground14) : ℤ :=
  (totalOmissions14 B J y : ℤ) - (occupiedTraces14 B J).card

private def ceilHalfPlusOne14 (n : ℕ) : ℕ :=
  (n + 2) / 2

private def ceilHalfPlusThree14 (n : ℕ) : ℕ :=
  (n + 4) / 2

/-- Claim 42271: the exact outside-trace deficit and one-return-per-fiber
arithmetic, with the tight/outside omission bounds attached only to the
particular deficit witness. -/
def claim42271 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      let J := R₁ ∪ R₂
      let B := residualBlock14 G R₁ R₂
      fiberPartition14 B J ∧
        (∀ y : Ground14,
          delta14 B y = traceDeficitSum14 B J y) ∧
        topReturnAlignment14 G B R₁ R₂ J ∧
        (∀ y : Ground14, y ∉ J →
          outsideFiberConstant14 B J y ∧
            jReturnPreservesOutsideCoordinate14 B J y) ∧
        (∀ y : Ground14, y ∈ J →
          (∀ Z ∈ occupiedTraces14 B J,
            ∃ A : Finset Ground14,
              A ∈ traceFiber14 B J Z ∧ y ∉ A) ∧
          totalOmissions14 B J y ≥ (occupiedTraces14 B J).card ∧
          topReturnResidual14 B J y +
              (occupiedTraces14 B J).card = totalOmissions14 B J y) ∧
        (∃ y : Ground14,
          delta14 B y ≥ delta14 G y ∧
          ((y ∈ tight14 p₀ p₁ p₂ →
              totalOmissions14 B J y ≥ ceilHalfPlusOne14 B.card) ∧
            (y ∉ tight14 p₀ p₁ p₂ →
              totalOmissions14 B J y ≥ ceilHalfPlusThree14 B.card)))

end MathlibPlus.Open.ResearchFormalization.R2667Claim42271
