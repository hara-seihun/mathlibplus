import MathlibPlus.Open.Combinatorics.R2667.Claim42272

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42265

open MathlibPlus.Open.Combinatorics.UnionClosedBatch

abbrev Ground14 := MathlibPlus.Open.Combinatorics.R2667.Claim42272.Ground14
abbrev Family14 := MathlibPlus.Open.Combinatorics.R2667.Claim42272.Family14

abbrev exactEndpoint14 :=
  MathlibPlus.Open.Combinatorics.R2667.Claim42272.exactEndpoint14

def lowerSubfamily14 (G : Family14) (R : Finset Ground14) : Family14 :=
  G.filter (fun A => A ⊆ R)

def upperSubfamily14 (G : Family14) (R : Finset Ground14) : Family14 :=
  G.filter (fun A => R ⊆ A)

def generatedP14 (G : Family14)
    (R₁ R₂ : Finset Ground14) : Family14 :=
  let D₁ := lowerSubfamily14 G R₁
  let D₂ := lowerSubfamily14 G R₂
  (D₁.product D₂).image (fun q => q.1 ∪ q.2)

def generatedK1K2Union14 (G : Family14)
    (R₁ R₂ : Finset Ground14) : Family14 :=
  upperSubfamily14 G R₁ ∪ upperSubfamily14 G R₂

def coupledFamily14 (G : Family14)
    (R₁ R₂ : Finset Ground14) : Family14 :=
  generatedP14 G R₁ R₂ ∪ upperSubfamily14 G R₁ ∪ upperSubfamily14 G R₂

def claim42265 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      let J := R₁ ∪ R₂
      let P := generatedP14 G R₁ R₂
      let K₁ := upperSubfamily14 G R₁
      let K₂ := upperSubfamily14 G R₂
      let C := coupledFamily14 G R₁ R₂
      unionClosed P ∧
        unionClosed (K₁ ∪ K₂) ∧
        (∀ ⦃A B : Finset Ground14⦄,
          A ∈ P → B ∈ K₁ → A ∪ B ∈ K₁) ∧
        (∀ ⦃A B : Finset Ground14⦄,
          A ∈ P → B ∈ K₂ → A ∪ B ∈ K₂) ∧
        (∀ ⦃A B : Finset Ground14⦄,
          A ∈ K₁ → B ∈ K₂ →
            J ⊆ A ∪ B ∧ A ∪ B ∈ K₁ ∩ K₂) ∧
        unionClosed C

end MathlibPlus.Open.Combinatorics.R2667.Claim42265
