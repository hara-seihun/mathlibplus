import MathlibPlus.Open.ResearchFormalization.R0992Claim28032

namespace MathlibPlus.Open.ResearchFormalization.R0992Claim28035

noncomputable section

abbrev F3 := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.F3
abbrev Plane := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.Plane
abbrev Fibre := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.Fibre
abbrev E := MathlibPlus.Open.ResearchFormalization.R0992Claim28032.E

open MathlibPlus.Open.ResearchFormalization.R0992Claim28032
open MathlibPlus.Open.Research.OrbitalCriteria

def baseValueLevelSetContained (F : Plane → Fibre) : Prop :=
  ∀ x : Plane, F x = F 0 → x = 0 ∨ x = ![1, 0]

def correctedPolarSpanCondition (F : Plane → Fibre) : Prop :=
  ∀ x : Plane, F x = F 0 → quadraticQ x = 0

/-- The set-level conjugation relation used for the displayed `T^{q}`. -/
def conjugatesTranslation (c q : Equiv.Perm E) : Prop :=
  Set.image (fun h : Equiv.Perm E => c⁻¹ * h * c)
      (translationGroup : Set (Equiv.Perm E)) =
    conjugateSet q (translationGroup : Set (Equiv.Perm E))

def translationConjugacyInsideTwoClosure (F : Plane → Fibre) : Prop :=
  let q := transporter F
  let G := generatedGroup q
  q ∈ twoClosureOf (G : Set (Equiv.Perm E)) ∧
    ∃ c : Equiv.Perm E,
      c ∈ twoClosureOf (G : Set (Equiv.Perm E)) ∧
        conjugatesTranslation c q

/-- Claim 28035: the corrected polar-span/base-level-set criterion gives
internal conjugacy of the regular pair inside the exact generated-pair
2-closure, and the raw-table census is the stated one. -/
def correctedPolarSpanCriterion_claim28035 : Prop :=
  (∀ F : Plane → Fibre,
    correctedPolarSpanCondition F ↔ baseValueLevelSetContained F) ∧
    (∀ F : Plane → Fibre,
      correctedPolarSpanCondition F → translationConjugacyInsideTwoClosure F) ∧
    Nat.card {F : Plane → Fibre // correctedPolarSpanCondition F} =
      27 ^ 2 * 26 ^ 7 ∧
    27 ^ 2 * 26 ^ 7 = (5855189618304 : ℕ)

end
end MathlibPlus.Open.ResearchFormalization.R0992Claim28035
