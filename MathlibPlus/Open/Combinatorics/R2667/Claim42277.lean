import MathlibPlus.Open.Combinatorics.UnionClosedBatch

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42277

open MathlibPlus.Open.Combinatorics.UnionClosedBatch

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

def lowerLayer14 (G : Family14) (p₀ : Ground14) : Family14 :=
  G.filter (fun A => p₀ ∉ A)

def upperLayer14 (G : Family14) (p₀ : Ground14) : Family14 :=
  (G.filter (fun A => p₀ ∈ A)).image (fun A => A.erase p₀)

def oppositeWitness14
    (G : Family14) (p₀ p₁ p₂ : Ground14) : Prop :=
  let L := lowerLayer14 G p₀
  let U := upperLayer14 G p₀
  ∃ x z : Ground14,
    x ≠ z ∧
    x ≠ p₀ ∧
    z ≠ p₀ ∧
    frequency L x ≥ 14 ∧
    frequency U z ≥ 13 ∧
    frequency U x ≤
      (if x ∈ tight14 p₀ p₁ p₂ then 12 else 11) ∧
    frequency L z ≤
      (if z ∈ tight14 p₀ p₁ p₂ then 13 else 12)

/-- Claim 42277: the minimum-cardinality endpoint supplies distinct reduced
coordinates with the exact opposite-polarity lower bounds and caps. -/
def claim42277 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      oppositeWitness14 G p₀ p₁ p₂

end MathlibPlus.Open.Combinatorics.R2667.Claim42277
