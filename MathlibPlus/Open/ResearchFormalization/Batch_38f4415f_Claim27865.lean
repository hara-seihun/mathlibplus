import Mathlib
import MathlibPlus.Open.Research.CIAtlas

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27865

private abbrev G72 := MathlibPlus.Open.Research.CIAtlas.C2CubedC9

private def connectionSet13 (S : Finset G72) : Prop :=
  MathlibPlus.Open.Research.CIAtlas.connectionSet72 13 S

private def graphPermutation (S : Finset G72) :=
  {e : Equiv.Perm G72 //
    ∀ x y,
      MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S x y ↔
        MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S (e x) (e y)}

private def sameBase (x y : G72) : Prop :=
  x.2.2.2 = y.2.2.2

private def preservesPartition (S : Finset G72)
    (φ : graphPermutation S) : Prop :=
  ∀ x y, sameBase x y ↔ sameBase (φ.1 x) (φ.1 y)

private def partitionBreaking (S : Finset G72) : Prop :=
  ∃ φ : graphPermutation S, ¬preservesPartition S φ

private def partitionPreserving (S : Finset G72) : Prop :=
  ∀ φ : graphPermutation S, preservesPartition S φ

private def normalPresentation (S : Finset G72) : Prop :=
  ∀ φ : graphPermutation S, ∀ g : G72, ∃ h : G72, ∀ x : G72,
    φ.1 (g + φ.1.symm x) = h + x

private def nonlinearBase (S : Finset G72) : Prop :=
  partitionPreserving S ∧ ¬normalPresentation S ∧
    ∃ φ : graphPermutation S, ∃ β : Equiv.Perm (ZMod 9),
      preservesPartition S φ ∧
      (∀ x : G72, (φ.1 x).2.2.2 = β (x.2.2.2)) ∧
      β 0 = 0 ∧
      ¬∃ e : AddEquiv (ZMod 9) (ZMod 9), ∀ b, e b = β b

private def ambientException (S : Finset G72) : Prop :=
  partitionBreaking S ∨ nonlinearBase S

private def exceptionType (S : Finset G72) : Prop :=
  ∃ U : Finset G72,
    connectionSet13 U ∧ ambientException U ∧
      MathlibPlus.Open.Research.CIAtlas.graphEquivalent72 S U

private def exceptionRepresentatives : Prop :=
  ∃ R : Finset (Finset G72),
    R.card = 2902 ∧
    (∀ S, connectionSet13 S →
      ¬(partitionBreaking S ∧ nonlinearBase S)) ∧
    (∀ T, T ∈ R → connectionSet13 T ∧ exceptionType T) ∧
    (∀ S, connectionSet13 S → exceptionType S →
      ∃! T, T ∈ R ∧ connectionSet13 T ∧ exceptionType T ∧
        MathlibPlus.Open.Research.CIAtlas.graphEquivalent72 S T)

/-- The 2,902 valency-13 graph types in the two ambient recognition
    exception classes have one Aut(G)-presentation orbit in every graph fiber. -/
def claim27865 : Prop :=
  exceptionRepresentatives ∧
    ∀ S T : Finset G72,
      connectionSet13 S → connectionSet13 T → exceptionType S →
      MathlibPlus.Open.Research.CIAtlas.graphEquivalent72 S T →
      MathlibPlus.Open.Research.CIAtlas.autEquivalent72 S T

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim27865
