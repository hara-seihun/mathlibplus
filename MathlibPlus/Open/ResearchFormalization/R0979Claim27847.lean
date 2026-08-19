import Mathlib
import MathlibPlus.Open.Research.CIAtlas

namespace MathlibPlus.Open.ResearchFormalization.R0979Claim27847

noncomputable section
open Classical

abbrev G27847 := MathlibPlus.Open.Research.CIAtlas.C2CubedC9

private def connectionSet27847 (S : Finset G27847) : Prop :=
  MathlibPlus.Open.Research.CIAtlas.connectionSet72 12 S

private def graphPermutation27847 (S : Finset G27847) :=
  {e : Equiv.Perm G27847 //
    ∀ x y,
      MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S x y ↔
        MathlibPlus.Open.Research.CIAtlas.graphAdjacent72 S (e x) (e y)}

private def normalPresentation27847 (S : Finset G27847) : Prop :=
  ∀ φ : graphPermutation27847 S, ∀ g : G27847, ∃ h : G27847, ∀ x : G27847,
    φ.1 (g + φ.1.symm x) = h + x

private def graphTypeAndPresentationCarrier27847
    (P R : Finset (Finset G27847)) : Prop :=
  P.card = 16992 ∧
    R.card = 16992 ∧
    (∀ T, T ∈ P → connectionSet27847 T) ∧
    (∀ T, T ∈ R → connectionSet27847 T) ∧
    (∀ S, connectionSet27847 S →
      ∃! T, T ∈ P ∧ connectionSet27847 T ∧
        MathlibPlus.Open.Research.CIAtlas.autEquivalent72 S T) ∧
    (∀ S, connectionSet27847 S →
      ∃! T, T ∈ R ∧ connectionSet27847 T ∧
        MathlibPlus.Open.Research.CIAtlas.graphEquivalent72 S T) ∧
    (∀ S T, connectionSet27847 S → connectionSet27847 T →
      (MathlibPlus.Open.Research.CIAtlas.graphEquivalent72 S T ↔
        MathlibPlus.Open.Research.CIAtlas.autEquivalent72 S T))

/-- Claim 27847: on the reviewed valency-twelve presentation and ordinary
    graph-type carriers, exactly 13,954 presentations are normal and 3,038
    are nonnormal. -/
def claim27847 : Prop :=
  ∃ P R : Finset (Finset G27847),
    graphTypeAndPresentationCarrier27847 P R ∧
    (R.filter normalPresentation27847).card = 13954 ∧
    (R.filter (fun S => ¬ normalPresentation27847 S)).card = 3038

end
end MathlibPlus.Open.ResearchFormalization.R0979Claim27847
