import Mathlib
import MathlibPlus.Open.Research.CIAtlas

namespace MathlibPlus.Open.ResearchFormalization.Claim27851

noncomputable section

private abbrev G72 := MathlibPlus.Open.Research.CIAtlas.C2CubedC9

private def connectionSet12 (S : Finset G72) : Prop :=
  MathlibPlus.Open.Research.CIAtlas.connectionSet72 12 S

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

private def nonlinearIdentityFixedC9BaseStabilizer (S : Finset G72) : Prop :=
  partitionPreserving S ∧
    ¬normalPresentation S ∧
    ∃ φ : graphPermutation S, ∃ β : Equiv.Perm (ZMod 9),
      preservesPartition S φ ∧
      (∀ x : G72, (φ.1 x).2.2.2 = β (x.2.2.2)) ∧
      β 0 = 0 ∧
      ¬∃ e : AddEquiv (ZMod 9) (ZMod 9), ∀ b, e b = β b

private def graphTypeRepresentatives12 (R : Finset (Finset G72)) : Prop :=
  R.card = 16992 ∧
    (∀ T, T ∈ R → connectionSet12 T) ∧
    (∀ S, connectionSet12 S →
      ∃! T, T ∈ R ∧ connectionSet12 T ∧
        MathlibPlus.Open.Research.CIAtlas.graphEquivalent72 S T)

/-- Claim 27851: the connected valency-twelve graph-type census has 559
    partition-breaking types and 57 nonlinear identity-fixed base-action
    types, both on the complete graph-type representative carrier. -/
def claim27851 : Prop :=
  ∃ R : Finset (Finset G72),
    graphTypeRepresentatives12 R ∧
    Nat.card {S : Finset G72 //
      S ∈ R ∧ MathlibPlus.Open.Research.CIAtlas.graphConnected72 S ∧
      partitionBreaking S} = 559 ∧
    Nat.card {S : Finset G72 //
      S ∈ R ∧ MathlibPlus.Open.Research.CIAtlas.graphConnected72 S ∧
        nonlinearIdentityFixedC9BaseStabilizer S} = 57

end
end MathlibPlus.Open.ResearchFormalization.Claim27851
