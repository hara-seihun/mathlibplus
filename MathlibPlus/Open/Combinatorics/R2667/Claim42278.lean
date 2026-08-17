import MathlibPlus.Open.Combinatorics.UnionClosedBatch

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42278

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

def familyUnion14 (L U : Family14) : Family14 :=
  (L.product U).image (fun q => q.1 ∪ q.2)

def lowerUpperClosed14 (L U : Family14) : Prop :=
  familyUnion14 L U ⊆ U

def lowerRootAction14 (L : Family14) (R : Finset Ground14) : Prop :=
  ∀ ⦃A : Finset Ground14⦄,
    A ∈ L → ¬ A ⊆ R → A ∪ R ∈ L

def upperRootAction14 (U : Family14) (R : Finset Ground14) : Prop :=
  ∀ ⦃A : Finset Ground14⦄, A ∈ U → A ∪ R ∈ U

/-- Commutation of the partial lower maps and total upper maps, including
membership of every intermediate and final layer value. -/
def rootActionsCommute14
    (L U : Family14) (R₁ R₂ : Finset Ground14) : Prop :=
  (∀ ⦃A : Finset Ground14⦄, A ∈ L →
      ¬ A ⊆ R₁ → ¬ A ⊆ R₂ →
      ¬ (A ∪ R₁) ⊆ R₂ → ¬ (A ∪ R₂) ⊆ R₁ →
      (A ∪ R₁) ∪ R₂ ∈ L ∧
        (A ∪ R₂) ∪ R₁ ∈ L ∧
        (A ∪ R₁) ∪ R₂ = (A ∪ R₂) ∪ R₁) ∧
    (∀ ⦃A : Finset Ground14⦄, A ∈ U →
      (A ∪ R₁) ∪ R₂ ∈ U ∧
        (A ∪ R₂) ∪ R₁ ∈ U ∧
        (A ∪ R₁) ∪ R₂ = (A ∪ R₂) ∪ R₁)

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

/-- Claim 42278: the exact endpoint carries the 27/26 bimodule, both root
extension laws, layer-preserving commuting root actions, and the distinct
opposite-polarity witnesses. -/
def claim42278 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      let L := lowerLayer14 G p₀
      let U := upperLayer14 G p₀
      L.card = 27 ∧
        U.card = 26 ∧
        unionClosed L ∧
        unionClosed U ∧
        lowerUpperClosed14 L U ∧
        lowerRootAction14 L R₁ ∧
        lowerRootAction14 L R₂ ∧
        upperRootAction14 U R₁ ∧
        upperRootAction14 U R₂ ∧
        rootActionsCommute14 L U R₁ R₂ ∧
        oppositeWitness14 G p₀ p₁ p₂

end MathlibPlus.Open.Combinatorics.R2667.Claim42278
