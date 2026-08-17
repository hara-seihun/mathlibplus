import MathlibPlus.Open.Combinatorics.UnionClosedBatch

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42272

open MathlibPlus.Open.Combinatorics.UnionClosedBatch
open scoped BigOperators

abbrev Ground14 := Fin 14
abbrev Family14 := Family 14

def tight14 (p₀ p₁ p₂ : Ground14) : Finset Ground14 :=
  {p₀, p₁, p₂}

def rootExtension14 (G : Family14) (R : Finset Ground14) : Prop :=
  ∀ ⦃A : Finset Ground14⦄, A ∈ G → ¬ A ⊆ R → A ∪ R ∈ G

def exactEndpoint14 (G : Family14)
    (p₀ p₁ p₂ : Ground14) (R₁ R₂ : Finset Ground14) : Prop :=
  minimumActualGroundCounterexample G ∧
    G.card = 53 ∧
    ground G = Finset.univ ∧
    p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₁ ≠ p₂ ∧
    frequency G p₀ = 26 ∧
    frequency G p₁ = 26 ∧
    frequency G p₂ = 26 ∧
    (∀ x : Ground14,
      x ∉ tight14 p₀ p₁ p₂ → frequency G x ≤ 25) ∧
    p₀ ∉ R₁ ∧ p₁ ∉ R₁ ∧ p₂ ∉ R₁ ∧
    p₀ ∉ R₂ ∧ p₁ ∉ R₂ ∧ p₂ ∉ R₂ ∧
    R₁ ∉ G ∧ R₂ ∉ G ∧
    R₁ ∪ R₂ ∈ G ∧
    rootExtension14 G R₁ ∧ rootExtension14 G R₂ ∧
    unionClosed G

def coupledCore14 (G : Family14)
    (R₁ R₂ : Finset Ground14) : Family14 :=
  let D₁ := G.filter (fun A => A ⊆ R₁)
  let D₂ := G.filter (fun A => A ⊆ R₂)
  let K₁ := G.filter (fun A => R₁ ⊆ A)
  let K₂ := G.filter (fun A => R₂ ⊆ A)
  let P := (D₁.product D₂).image (fun q => q.1 ∪ q.2)
  P ∪ K₁ ∪ K₂

def residualBlock14 (G : Family14)
    (R₁ R₂ : Finset Ground14) : Family14 :=
  G \ coupledCore14 G R₁ R₂

def rootUpperFamily14 (G : Family14)
    (R : Finset Ground14) : Family14 :=
  G.filter (fun A => R ⊆ A)

def delta14 (F : Family14) (y : Ground14) : Int :=
  (F.card : Int) - 2 * (frequency F y : Int)

def outsideTrace14 (A J : Finset Ground14) : Finset Ground14 :=
  A \ J

def occupiedTraces14 (B : Family14) (J : Finset Ground14) :
    Finset (Finset Ground14) :=
  B.image (fun A => outsideTrace14 A J)

def traceFiber14 (B : Family14) (J Z : Finset Ground14) : Family14 :=
  B.filter (fun A => outsideTrace14 A J = Z)

def traceCount14 (B : Family14) (J Z : Finset Ground14) : ℕ :=
  (traceFiber14 B J Z).card

def traceCoordinateCount14
    (B : Family14) (J Z : Finset Ground14) (y : Ground14) : ℕ :=
  ((traceFiber14 B J Z).filter (fun A => y ∈ A)).card

def traceDeficitSum14
    (B : Family14) (J : Finset Ground14) (y : Ground14) : Int :=
  ∑ Z ∈ occupiedTraces14 B J,
    ((traceCount14 B J Z : Int) -
      2 * (traceCoordinateCount14 B J Z y : Int))

def outsideFiberConstant14
    (B : Family14) (J : Finset Ground14) (y : Ground14) : Prop :=
  ∀ ⦃A A' : Finset Ground14⦄,
    A ∈ B → A' ∈ B →
      outsideTrace14 A J = outsideTrace14 A' J →
        (y ∈ A ↔ y ∈ A')

def jReturnPreservesOutsideCoordinate14
    (B : Family14) (J : Finset Ground14) (y : Ground14) : Prop :=
  ∀ ⦃A : Finset Ground14⦄, A ∈ B →
    (y ∈ A ↔ y ∈ A ∪ J)

def jReturnCollision14 (J : Finset Ground14) : Prop :=
  ∀ A A' : Finset Ground14,
    A ∪ J = A' ∪ J ↔ A \ J = A' \ J

/-- Claim 42272: for every outside-`J` coordinate, its membership is constant
on each outside-trace fibre, its integer deficit is the exact fibre sum, and
adjoining J leaves that coordinate unchanged. -/
def claim42272 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      let J := R₁ ∪ R₂
      let B := residualBlock14 G R₁ R₂
      jReturnCollision14 J ∧
        (∀ y : Ground14, y ∉ J →
          outsideFiberConstant14 B J y ∧
            jReturnPreservesOutsideCoordinate14 B J y ∧
            delta14 B y = traceDeficitSum14 B J y ∧
            (delta14 B y ≥ delta14 G y →
              jReturnPreservesOutsideCoordinate14 B J y)) ∧
        (∀ ⦃A : Finset Ground14⦄, A ∈ B →
          A ∪ R₁ ∈ rootUpperFamily14 G R₁ ∧
          A ∪ R₂ ∈ rootUpperFamily14 G R₂ ∧
          A ∪ J ∈ rootUpperFamily14 G R₁ ∧
          A ∪ J ∈ rootUpperFamily14 G R₂)

end MathlibPlus.Open.Combinatorics.R2667.Claim42272
