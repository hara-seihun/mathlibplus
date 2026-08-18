import MathlibPlus.Open.ResearchFormalization.R0334.Claim20021

namespace MathlibPlus.Open.ResearchFormalization.R0334.Claim20022

noncomputable section

open Classical
open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0334.Claim20021

private abbrev FactorFamily (α : Type*) :=
  Fin 2 → Finset (Finset α)

private noncomputable def ordinaryImage {α : Type*}
    [DecidableEq α] (C : FactorFamily α) : Finset (Finset α) :=
  productFamily C

private def coordinateDeficit {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : ℚ :=
  (deficitProduct F x : ℚ)

private def factorSize {α : Type*} [DecidableEq α]
    (C : FactorFamily α) (i : Fin 2) : ℚ :=
  (C i).card

private def factorDeficit {α : Type*} [DecidableEq α]
    (C : FactorFamily α) (i : Fin 2) (x : α) : ℚ :=
  (deficitProduct (C i) x : ℚ)

private def sharedCoordinateProduct {α : Type*}
    [DecidableEq α] (C : FactorFamily α) (x : α) : Prop :=
  factorHasEmpty C ∧
    factorUnionClosed C ∧
      injectiveProduct C ∧
        x ∈ familySupport (C 0) ∧
          x ∈ familySupport (C 1)

private def witnessFactorZero : Finset (Finset (Fin 5)) :=
  {∅, {4}, {0, 3, 4}}

private def witnessFactorOne : Finset (Finset (Fin 5)) :=
  {∅, {1}, {0, 1, 2}}

private def witnessFactors : FactorFamily (Fin 5) :=
  fun i => if i = 0 then witnessFactorZero else witnessFactorOne

private def explicitPositiveFactorNonpositiveProduct : Prop :=
  sharedCoordinateProduct witnessFactors 0 ∧
    0 < factorDeficit witnessFactors 0 0 ∧
      0 < factorDeficit witnessFactors 1 0 ∧
        coordinateDeficit (ordinaryImage witnessFactors) 0 ≤ 0

/-- Claim 20022: for an injective ordinary set-union image of two finite
union-closed empty-containing factors sharing `x`, the exact centered deficit
has the mixed term displayed in the claim; positive factor deficits are
necessary, but the explicit same-carrier witness shows they are not sufficient. -/
def sharedCoordinateMixedDeficit_claim20022 : Prop :=
  (∀ {α : Type*} [DecidableEq α]
    (C : FactorFamily α) (x : α),
    sharedCoordinateProduct C x →
      let P := ordinaryImage C
      let n₀ := factorSize C 0
      let n₁ := factorSize C 1
      let d₀ := factorDeficit C 0 x
      let d₁ := factorDeficit C 1 x
      coordinateDeficit P x =
          (d₀ * n₁ + d₁ * n₀ + d₀ * d₁ - n₀ * n₁) / 2 ∧
        (0 < coordinateDeficit P x → 0 < d₀ ∧ 0 < d₁)) ∧
    explicitPositiveFactorNonpositiveProduct

end

end MathlibPlus.Open.ResearchFormalization.R0334.Claim20022
