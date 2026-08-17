import MathlibPlus.Open.ResearchFormalization.R0630
import MathlibPlus.Combinatorics.Claim42226Definitions

namespace MathlibPlus.Open.ResearchFormalization.R2662

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Combinatorics.Claim42226

/-- The outside-support family of a finite set family relative to `M`. -/
def outsideSupports {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) : Set (Finset α) :=
  {S | ∃ A : Finset α, A ∈ F ∧ outsideSupport M A = S}

/-- A support carrying a prescribed trace type. -/
def supportCarriesTrace {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M S : Finset α)
    (R : Set (Finset α)) : Prop :=
  S ∈ outsideSupports F M ∧
    outsideSupportTraceFiber F M S = R

def neutralTrace {α : Type*} (M : Finset α) : Set (Finset α) :=
  {∅, M}

def singletonTrace {α : Type*} (M : Finset α) (m : α) : Set (Finset α) :=
  {∅, {m}, M}

def fullTrace {α : Type*} (M : Finset α) : Set (Finset α) :=
  {T | T ⊆ M}

/-- The exact five-type profile around a three-element member. -/
def deficitNineTraceProfile {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (k : ℕ)
    (m : Fin 3 → α) : Prop :=
  M ∈ F ∧ M.card = 3 ∧ M = {m 0, m 1, m 2} ∧
    (∀ i j : Fin 3, i ≠ j → m i ≠ m j) ∧
    Set.ncard {S | supportCarriesTrace F M S (neutralTrace M)} = k ∧
    (∀ i : Fin 3,
      ∃! S, supportCarriesTrace F M S (singletonTrace M (m i))) ∧
    (∃! C, supportCarriesTrace F M C (fullTrace M)) ∧
    (∀ S, S ∈ outsideSupports F M →
      outsideSupportTraceFiber F M S = neutralTrace M ∨
      (∃ i : Fin 3,
        outsideSupportTraceFiber F M S = singletonTrace M (m i)) ∨
      outsideSupportTraceFiber F M S = fullTrace M)

/-- The number of neutral supports containing an outside coordinate. -/
def neutralMultiplicity {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (y : α) : ℕ :=
  Set.ncard {S |
    supportCarriesTrace F M S (neutralTrace M) ∧ y ∈ S}

/-- The number of singleton-trace carriers containing an outside coordinate. -/
def singletonMultiplicity {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α)
    (m : Fin 3 → α) (y : α) : ℕ :=
  Set.ncard {S |
    (∃ i : Fin 3,
      supportCarriesTrace F M S (singletonTrace M (m i))) ∧ y ∈ S}

/-- Frequency of an outside coordinate in the support family. -/
def outsideFrequency {α : Type*} [DecidableEq α]
    (Sigma : Set (Finset α)) (y : α) : ℕ :=
  Set.ncard {S | S ∈ Sigma ∧ y ∈ S}

/-- The actual ground of a support family. -/
def outsideGround {α : Type*}
    (Sigma : Set (Finset α)) : Set α :=
  {y | ∃ S ∈ Sigma, y ∈ S}

/-- Ordinary union-closure for a set of finite supports. -/
def outsideUnionClosed {α : Type*} [DecidableEq α]
    (Sigma : Set (Finset α)) : Prop :=
  ∀ ⦃S T : Finset α⦄, S ∈ Sigma → T ∈ Sigma → S ∪ T ∈ Sigma

/-- No abundant coordinate in a finite support family. -/
def outsideNoAbundant {α : Type*} [DecidableEq α]
    (Sigma : Set (Finset α)) : Prop :=
  ∀ y ∈ outsideGround Sigma,
    2 * outsideFrequency Sigma y < Set.ncard Sigma

/-- Claim 42228: the unique singleton-trace carriers pairwise cover the
unique full-trace carrier. -/
def singletonCarriersCover_claim42228 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (k : ℕ) (m : Fin 3 → α),
    F.Nonempty → unionClosed F →
    deficitNineTraceProfile F M k m →
    ∀ i j : Fin 3, i ≠ j →
      ∀ Sᵢ Sⱼ C : Finset α,
        supportCarriesTrace F M Sᵢ (singletonTrace M (m i)) →
        supportCarriesTrace F M Sⱼ (singletonTrace M (m j)) →
        supportCarriesTrace F M C (fullTrace M) →
        Sᵢ ∪ Sⱼ = C

/-- Claim 42231: the weighted frequency formula on the original family. -/
def weightedOutsideFrequency_claim42231 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (k : ℕ) (m : Fin 3 → α),
    F.Nonempty → unionClosed F →
    deficitNineTraceProfile F M k m →
    ∀ C : Finset α,
      supportCarriesTrace F M C (fullTrace M) →
      ∀ y ∈ C,
        coordinateFrequency F y =
          2 * neutralMultiplicity F M y +
            3 * singletonMultiplicity F M m y + 8

/-- Claim 42232: nonabundance in `F` gives strict half-frequency in the
outside-support family, with the exact deficit-nine inequalities. -/
def strictOutsideNonabundance_claim42232 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (k : ℕ) (m : Fin 3 → α),
    F.Nonempty → unionClosed F → noAbundantCoordinate F →
    deficitNineTraceProfile F M k m →
    Set.ncard (outsideSupports F M) = k + 4 ∧ F.card = 2 * k + 17 ∧
      ∀ C : Finset α,
        supportCarriesTrace F M C (fullTrace M) →
        ∀ y ∈ C,
          let a := neutralMultiplicity F M y
          let r := singletonMultiplicity F M m y
          let fSigma := outsideFrequency (outsideSupports F M) y
          (r = 2 ∨ r = 3) ∧
            2 * a + 3 * r + 8 ≤ k + 8 ∧
            2 * a + 3 * r ≤ k ∧
            fSigma = a + r + 1 ∧
            2 * fSigma = 2 * a + 2 * r + 2 ∧
            2 * fSigma ≤ k - r + 2 ∧
            k - r + 2 ≤ k ∧
            k < k + 4 ∧
            2 * fSigma < Set.ncard (outsideSupports F M)

/-- Claim 42234: the exact deficit-nine profile contracts to a smaller
ordinary union-closed support family with no abundant ground coordinate. -/
def deficitNineProfileContraction_claim42234 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (k : ℕ) (m : Fin 3 → α),
    F.Nonempty → unionClosed F → noAbundantCoordinate F →
    deficitNineTraceProfile F M k m →
    let Sigma := outsideSupports F M
    Sigma.Finite ∧
      outsideUnionClosed Sigma ∧
      outsideNoAbundant Sigma ∧
      Set.ncard Sigma < F.card

end

end MathlibPlus.Open.ResearchFormalization.R2662
