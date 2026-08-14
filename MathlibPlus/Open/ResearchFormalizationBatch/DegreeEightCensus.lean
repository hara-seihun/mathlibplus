import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.DegreeEightCensus

abbrev degreeEightPoint := Fin 8
abbrev permutationGroup := Equiv.Perm degreeEightPoint

def transitiveDegreeEight (H : Subgroup permutationGroup) : Prop :=
  ∀ x y : degreeEightPoint, ∃ g : H, (g : permutationGroup) x = y

def regularCyclicEight (H : Subgroup permutationGroup) : Prop :=
  Nat.card H = 8 ∧
    Function.Bijective (fun g : H => (g : permutationGroup) 0)

def containsRegularCyclicEight (H : Subgroup permutationGroup) : Prop :=
  ∃ g : H, regularCyclicEight (Subgroup.zpowers (g : permutationGroup))

def permutationConjugate
    (H K : Subgroup permutationGroup) : Prop :=
  ∃ q : permutationGroup,
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) H = K

def degreeEightTransitiveGroupCensus : Prop := by
  classical
  exact
    ∃ representatives : Finset (Subgroup permutationGroup),
      representatives.card = 50 ∧
      (∀ H ∈ representatives, transitiveDegreeEight H) ∧
      (∀ H, transitiveDegreeEight H →
        ∃ R ∈ representatives, permutationConjugate H R) ∧
      (∀ R ∈ representatives, ∀ S ∈ representatives,
        permutationConjugate R S → R = S) ∧
      (representatives.filter containsRegularCyclicEight).card = 18

def degreeEightTransitiveGroupCensusDuplicate : Prop := by
  classical
  exact
    ∃ representatives : Finset (Subgroup permutationGroup),
      representatives.card = 50 ∧
      (∀ H ∈ representatives, transitiveDegreeEight H) ∧
      (∀ H, transitiveDegreeEight H →
        ∃ R ∈ representatives, permutationConjugate H R) ∧
      (∀ R ∈ representatives, ∀ S ∈ representatives,
        permutationConjugate R S → R = S) ∧
      (representatives.filter containsRegularCyclicEight).card = 18

end MathlibPlus.Open.ResearchFormalizationBatch.DegreeEightCensus
