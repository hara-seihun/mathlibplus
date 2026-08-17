import Mathlib
import MathlibPlus.Open.Research.CIAtlas

namespace MathlibPlus.Open.ResearchFormalization.R0980

noncomputable section

open Classical

abbrev G27863 := MathlibPlus.Open.Research.CIAtlas.C2CubedC9

def connectionSet13_27863 (S : Finset G27863) : Prop :=
  MathlibPlus.Open.Research.CIAtlas.connectionSet72 13 S

def graphPermutation27863 (S : Finset G27863) :=
  {e : Equiv.Perm G27863 //
    ∀ x y,
      MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S x y ↔
        MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S (e x) (e y)}

def sameC9Base27863 (x y : G27863) : Prop :=
  x.2.2.2 = y.2.2.2

def preservesNaturalPartition27863 (S : Finset G27863)
    (φ : graphPermutation27863 S) : Prop :=
  ∀ x y, sameC9Base27863 x y ↔ sameC9Base27863 (φ.1 x) (φ.1 y)

def partitionBreaking27863 (S : Finset G27863) : Prop :=
  ∃ φ : graphPermutation27863 S,
    ¬ preservesNaturalPartition27863 S φ

def partitionPreserving27863 (S : Finset G27863) : Prop :=
  ∀ φ : graphPermutation27863 S,
    preservesNaturalPartition27863 S φ

def normalPresentation27863 (S : Finset G27863) : Prop :=
  ∀ φ : graphPermutation27863 S, ∀ g : G27863, ∃ h : G27863, ∀ x : G27863,
    φ.1 (g + φ.1.symm x) = h + x

def nonlinearBase27863 (S : Finset G27863) : Prop :=
  partitionPreserving27863 S ∧
    ¬ normalPresentation27863 S ∧
    ∃ φ : graphPermutation27863 S, ∃ β : Equiv.Perm (ZMod 9),
      preservesNaturalPartition27863 S φ ∧
      (∀ x : G27863, (φ.1 x).2.2.2 = β (x.2.2.2)) ∧
      β 0 = 0 ∧
      ¬ ∃ e : AddEquiv (ZMod 9) (ZMod 9), ∀ b, e b = β b

def ambientException27863 (S : Finset G27863) : Prop :=
  partitionBreaking27863 S ∨ nonlinearBase27863 S

def graphTypeRepresentatives27863
    (R : Finset (Finset G27863)) : Prop :=
  R.card = 35022 ∧
    (∀ T, T ∈ R → connectionSet13_27863 T) ∧
    (∀ S, connectionSet13_27863 S →
      ∃! T, T ∈ R ∧ connectionSet13_27863 T ∧
        MathlibPlus.Open.Research.CIAtlas.graphEquivalent72 S T)

/-- The ambient-recognition census for the valency-thirteen graph types on
`C₂³ × C₉`, using the reviewed recognition predicates and graph-type carrier. -/
def claim27863 : Prop :=
  ∃ R : Finset (Finset G27863),
    graphTypeRepresentatives27863 R ∧
    (∀ S, S ∈ R →
      partitionBreaking27863 S ∨ partitionPreserving27863 S) ∧
    (R.filter partitionBreaking27863).card = 2774 ∧
    (R.filter partitionPreserving27863).card = 32248 ∧
    (R.filter (fun S =>
      partitionPreserving27863 S ∧ nonlinearBase27863 S)).card = 128 ∧
    (∀ S, S ∈ R →
      ¬ (partitionBreaking27863 S ∧ nonlinearBase27863 S)) ∧
    (R.filter ambientException27863).card = 2902 ∧
    2774 + 128 = 2902

end
end MathlibPlus.Open.ResearchFormalization.R0980
