import Mathlib
import MathlibPlus.Open.Research.CIAtlas

namespace MathlibPlus.Open.ResearchFormalization.Claim27850

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
  partitionPreserving S ∧ ¬normalPresentation S ∧
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

/-- Claim 27850: on the exact ordinary graph-type representative carrier,
15,091 types preserve the natural `C₂³`-coset partition and 1,901 break it;
96 of the preserving types have a nonlinear identity-fixed `C₉` base
stabilizer, and the two disjoint exception classes total 1,997. -/
def claim27850 : Prop :=
  ∃ R : Finset (Finset G72),
    graphTypeRepresentatives12 R ∧
    Nat.card {S : Finset G72 // S ∈ R ∧ partitionPreserving S} = 15091 ∧
    Nat.card {S : Finset G72 // S ∈ R ∧ partitionBreaking S} = 1901 ∧
    Nat.card {S : Finset G72 //
      S ∈ R ∧ partitionPreserving S ∧
        nonlinearIdentityFixedC9BaseStabilizer S} = 96 ∧
    Nat.card {S : Finset G72 // S ∈ R ∧
      (partitionBreaking S ∨ nonlinearIdentityFixedC9BaseStabilizer S)} = 1997 ∧
    (∀ S : Finset G72, S ∈ R →
      ¬(partitionBreaking S ∧
        nonlinearIdentityFixedC9BaseStabilizer S)) ∧
    15091 + 1901 = (16992 : ℕ) ∧
    1901 + 96 = (1997 : ℕ)

end
end MathlibPlus.Open.ResearchFormalization.Claim27850
