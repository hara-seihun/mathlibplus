import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2668Claim42292

noncomputable section

abbrev ReducedGround := Fin 4
abbrev ReducedSet := Finset ReducedGround
abbrev ReducedFamily := Finset ReducedSet

/-- Ordinary pairwise union closure for a finite family of finite sets. -/
def unionClosed (F : ReducedFamily) : Prop :=
  ∀ ⦃A B : ReducedSet⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- The layerwise join used by the `L ⊎ U` notation. -/
def layerJoin (L U : ReducedFamily) : ReducedFamily :=
  (L.product U).image (fun p => p.1 ∪ p.2)

/-- The lower root-extension law, with the principal-root downset excluded. -/
def lowerRootExtension (L : ReducedFamily) (R : ReducedSet) : Prop :=
  ∀ ⦃A : ReducedSet⦄, A ∈ L → ¬ A ⊆ R → A ∪ R ∈ L

/-- The upper root-extension law. -/
def upperRootExtension (U : ReducedFamily) (R : ReducedSet) : Prop :=
  ∀ ⦃A : ReducedSet⦄, A ∈ U → A ∪ R ∈ U

/-- The bit mask of a subset of the reduced four-coordinate ground. -/
def reducedMask (A : ReducedSet) : ℕ :=
  ∑ i ∈ A, 2 ^ i.1

/-- The masks occurring in a finite family. -/
def familyMasks (F : ReducedFamily) : Finset ℕ :=
  F.image reducedMask

/-- A root is absent from both reduced layers. -/
def absentRoot (L U : ReducedFamily) (R : ReducedSet) : Prop :=
  R ∉ L ∧ R ∉ U

/-- Claim 42292: the exact reduced same-category bimodule fixture. -/
def claim42292 : Prop :=
  let L : ReducedFamily :=
    {∅, {0, 1, 2}, {0, 1, 2, 3}}
  let U : ReducedFamily :=
    {{0, 1, 3}, {0, 1, 2, 3}}
  let R₁ : ReducedSet := {0, 2, 3}
  let R₂ : ReducedSet := {1, 2, 3}
  let whole : ReducedSet := {0, 1, 2, 3}
  unionClosed L ∧
    unionClosed U ∧
    layerJoin L U = U ∧
    familyMasks L = {0, 7, 15} ∧
    familyMasks U = {11, 15} ∧
    reducedMask R₁ = 13 ∧
    reducedMask R₂ = 14 ∧
    absentRoot L U R₁ ∧
    absentRoot L U R₂ ∧
    R₁.card = 3 ∧
    R₂.card = 3 ∧
    R₁ ∪ R₂ = whole ∧
    whole ∈ L ∧
    (lowerRootExtension L R₁ ∧ upperRootExtension U R₁) ∧
    (lowerRootExtension L R₂ ∧ upperRootExtension U R₂)

end

end MathlibPlus.Open.ResearchFormalization.R2668Claim42292
