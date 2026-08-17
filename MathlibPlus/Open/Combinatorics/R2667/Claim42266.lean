import MathlibPlus.Open.Combinatorics.R2667.Claim42272

namespace MathlibPlus.Open.Combinatorics.R2667.Claim42266

open MathlibPlus.Open.Combinatorics.UnionClosedBatch
open MathlibPlus.Open.Combinatorics.R2667.Claim42272

abbrev Ground14 := Fin 14
abbrev Family14 := Family 14

def singletonP0TraceCell14
    (G : Family14) (p₀ p₁ p₂ : Ground14) : Family14 :=
  G.filter (fun A => A ∩ tight14 p₀ p₁ p₂ = {p₀})

def rootIncomparableFamily14
    (G : Family14) (R : Finset Ground14) : Family14 :=
  G.filter (fun A => ¬ A ⊆ R ∧ ¬ R ⊆ A)

/-- Claim 42266: the singleton-`p₀` trace cell is outside the coupled
core, and the residual block is incomparable with both roots. -/
def claim42266 : Prop :=
  ∀ (G : Family14) (p₀ p₁ p₂ : Ground14)
    (R₁ R₂ : Finset Ground14),
    exactEndpoint14 G p₀ p₁ p₂ R₁ R₂ →
      let D₁ := G.filter (fun A => A ⊆ R₁)
      let D₂ := G.filter (fun A => A ⊆ R₂)
      let K₁ := G.filter (fun A => R₁ ⊆ A)
      let K₂ := G.filter (fun A => R₂ ⊆ A)
      let P := (D₁.product D₂).image (fun q => q.1 ∪ q.2)
      let C := P ∪ K₁ ∪ K₂
      let B := G \ C
      let Q₁ := rootIncomparableFamily14 G R₁
      let Q₂ := rootIncomparableFamily14 G R₂
      let T₀ := singletonP0TraceCell14 G p₀ p₁ p₂
      T₀.Nonempty ∧
        (∀ A ∈ T₀, A ∉ P ∧ A ∉ K₁ ∧ A ∉ K₂) ∧
        C ⊆ G ∧ C ≠ G ∧ C.card < 53 ∧
        D₁ ∪ D₂ ⊆ P ∧
        (∀ A ∈ B,
          ¬ A ⊆ R₁ ∧ ¬ R₁ ⊆ A ∧
            ¬ A ⊆ R₂ ∧ ¬ R₂ ⊆ A) ∧
        B ⊆ Q₁ ∩ Q₂

end MathlibPlus.Open.Combinatorics.R2667.Claim42266
