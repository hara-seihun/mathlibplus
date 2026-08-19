import MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow

namespace MathlibPlus.Open.ResearchFormalization.R1405Claim38684

noncomputable section

open MathlibPlus.Open.ResearchBatch.Formalization_01a00175.Sylow

abbrev Degree300 := Fin 300
abbrev C5Squared := ZMod 5 × ZMod 5
abbrev A4 := alternatingGroup (Fin 4)
abbrev TargetGroup := C5Squared × A4
abbrev PermSubgroup := Subgroup (Equiv.Perm Degree300)

/-- Semiregularity: no nonidentity element of the subgroup fixes a point. -/
def semiregular (P : PermSubgroup) : Prop :=
  ∀ g : P, g.1 ≠ 1 → ∀ x : Degree300, g.1 x ≠ x

/-- The centralizer of `P` inside the ambient subgroup `Y`. -/
def centralizerInY (Y P : PermSubgroup) : PermSubgroup :=
  Y ⊓ Subgroup.centralizer (P : Set (Equiv.Perm Degree300))

/-- A subgroup of `Y` carrying a regular copy of `C₅² × A₄`. -/
def regularTargetSubgroup (Y R : PermSubgroup) : Prop :=
  R ≤ Y ∧
    Nonempty (R ≃* TargetGroup) ∧
      isRegularPermutationSubgroup R

/-- The exact semiregular `C₅²` centralizer hypothesis. -/
def strictCentralDirectFactorHypothesis (Y : PermSubgroup) : Prop :=
  ∀ P : PermSubgroup,
    P ≤ Y →
      semiregular P →
        Nonempty (P ≃* C5Squared) →
          Nat.card (centralizerInY Y P) < 300

/-- The parenthetical order-25 sufficient hypothesis. -/
def order25CentralDirectFactorHypothesis (Y : PermSubgroup) : Prop :=
  ∀ P : PermSubgroup,
    P ≤ Y →
      semiregular P →
        Nonempty (P ≃* C5Squared) →
          Nat.card (centralizerInY Y P) = 25

/-- Claim 38684: a strict centralizer bound excludes a regular
`C₅² × A₄` subgroup, and order-25 centralizers are a sufficient special case. -/
def claim38684 : Prop :=
  ∀ Y : PermSubgroup,
    (strictCentralDirectFactorHypothesis Y →
      ¬ ∃ R : PermSubgroup, regularTargetSubgroup Y R) ∧
    (order25CentralDirectFactorHypothesis Y →
      ¬ ∃ R : PermSubgroup, regularTargetSubgroup Y R)

end

end MathlibPlus.Open.ResearchFormalization.R1405Claim38684
