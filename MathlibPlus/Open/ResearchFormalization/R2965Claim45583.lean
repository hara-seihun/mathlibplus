import MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges

namespace MathlibPlus.Open.ResearchFormalization.R2965Claim45583

noncomputable section

abbrev F2 := ZMod 2
abbrev V := Fin 2 → F2
abbrev Subspace := Submodule F2 V
abbrev EdgeFlag := MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges.SubspaceEdge F2 2
abbrev Line := {L : Subspace // Module.finrank F2 L = 1}

private def v10 : V := ![1, 0]
private def v01 : V := ![0, 1]
private def v11 : V := ![1, 1]

private def lineVector (j : Fin 3) : V :=
  if j = 0 then v10 else if j = 1 then v01 else v11

private def line (j : Fin 3) : Subspace :=
  if j = 0 then Submodule.span F2 ({v10} : Set V)
  else if j = 1 then Submodule.span F2 ({v01} : Set V)
  else Submodule.span F2 ({v11} : Set V)

private def listedLineDescription : Prop :=
  ∀ j : Fin 3, ∀ x : V,
    x ∈ line j ↔ x = 0 ∨ x = lineVector j

private def lineSet : Set Subspace := {L | Module.finrank F2 L = 1}

private def edgeZero (e : EdgeFlag) : Prop :=
  e.1.1 = ⊥ ∧ Module.finrank F2 e.1.2 = 1

private def edgeOne (e : EdgeFlag) : Prop :=
  Module.finrank F2 e.1.1 = 1 ∧ e.1.2 = ⊤

private def edgeZeroSet : Set EdgeFlag := {e | edgeZero e}
private def edgeOneSet : Set EdgeFlag := {e | edgeOne e}

private def lowerPair (j : Fin 3) : Subspace × Subspace := (⊥, line j)
private def upperPair (j : Fin 3) : Subspace × Subspace := (line j, ⊤)

private def subspaceCover (L U : Subspace) : Prop :=
  L < U ∧ ∀ M : Subspace, L ≤ M → M ≤ U → M = L ∨ M = U

private def edgePairOrder (a b : Subspace × Subspace) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2

private def simultaneousCover (a b : Subspace × Subspace) : Prop :=
  subspaceCover a.1 b.1 ∧ subspaceCover a.2 b.2

private def lineEnumeration : Prop :=
  listedLineDescription ∧
    Set.Finite lineSet ∧ Set.ncard lineSet = 3 ∧
    (∀ j : Fin 3, Module.finrank F2 (line j) = 1) ∧
    (∀ L : Line, ∃ j : Fin 3, L.1 = line j) ∧
    (∀ j k : Fin 3, line j = line k → j = k)

private def edgeLevelEnumeration : Prop :=
  Set.Finite edgeZeroSet ∧ Set.ncard edgeZeroSet = 3 ∧
    Set.Finite edgeOneSet ∧ Set.ncard edgeOneSet = 3 ∧
    (∀ j : Fin 3, ∃ e : EdgeFlag, edgeZero e ∧ e.1 = lowerPair j) ∧
    (∀ e : EdgeFlag, edgeZero e → ∃ j : Fin 3, e.1 = lowerPair j) ∧
    (∀ j : Fin 3, ∃ e : EdgeFlag, edgeOne e ∧ e.1 = upperPair j) ∧
    (∀ e : EdgeFlag, edgeOne e → ∃ j : Fin 3, e.1 = upperPair j)

private def completeF2CoverBlock : Prop :=
  (∀ j k : Fin 3, simultaneousCover (lowerPair j) (upperPair k)) ∧
    (∀ j k : Fin 3, edgePairOrder (lowerPair j) (upperPair k))

/-- Claim 45583: the complete adjacent-subspace edge levels and their exact
simultaneous-cover relation for the three lines in `F₂²`. -/
def claim45583 : Prop :=
  Fintype.card V = 4 ∧
    lineEnumeration ∧
    edgeLevelEnumeration ∧
    completeF2CoverBlock

end
end MathlibPlus.Open.ResearchFormalization.R2965Claim45583
