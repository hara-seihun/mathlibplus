import MathlibPlus.Combinatorics.CompleteFiberCayley
import MathlibPlus.Open.ResearchFormalization.R1152

namespace MathlibPlus.Combinatorics.CayleyHallOrbitClaims

noncomputable section

private def connectionSet {A H : Type*} [Group A] [Group H] : Set (A × H) :=
  ({1} : Set A) ×ˢ ((Set.univ : Set H) \ ({1} : Set H))

private def fiberGraph {A H : Type*} [Group A] [Group H] :
    SimpleGraph (A × H) :=
  SimpleGraph.mulCayley (connectionSet (A := A) (H := H))

private def hallFactor {A H : Type*} [Group A] [Group H] :
    Subgroup (A × H) :=
  (⊤ : Subgroup A).prod (⊥ : Subgroup H)

private def hallOrderCoprime {A H : Type*} [Group A] [Group H]
    [Fintype A] [Fintype H] : Prop :=
  Nat.Coprime (Fintype.card A) (Fintype.card H)

private def hallBlock {A H : Type*} (h : H) : Set (A × H) :=
  {x | x.2 = h}

private def regularOrbit {A H : Type*} [Group A] [Group H]
    (P : Subgroup (A × H)) (x : A × H) : Set (A × H) :=
  {y | ∃ p : A × H, p ∈ (P : Set (A × H)) ∧ y = x * p}

private def graphAutomorphism {V : Type*}
    (G : SimpleGraph V) (e : Equiv.Perm V) : Prop :=
  ∀ x y : V, G.Adj x y ↔ G.Adj (e x) (e y)

private def blockTranspositionMoves {A H : Type*}
    [Group A] [Group H] [Fintype A] [Fintype H]
    [DecidableEq A] [DecidableEq H] [Nontrivial A] [Nontrivial H] : Prop :=
  ∀ (a₀ : A) (h₁ h₂ : H), h₁ ≠ h₂ →
    let e : Equiv.Perm (A × H) := Equiv.swap (a₀, h₁) (a₀, h₂)
    graphAutomorphism (fiberGraph (A := A) (H := H)) e ∧
      e '' hallBlock h₁ =
        (hallBlock h₁ \ {(a₀, h₁)}) ∪ {(a₀, h₂)} ∧
      ∀ h : H, e '' hallBlock h₁ ≠ hallBlock h

private def connectionSetAdmissible {A H : Type*} [Group A] [Group H] : Prop :=
  (1 : A × H) ∉ connectionSet (A := A) (H := H) ∧
    ∀ s : A × H, s ∈ connectionSet (A := A) (H := H) →
      s⁻¹ ∈ connectionSet (A := A) (H := H)

private def regularHallOrbitPartition {A H : Type*}
    [Group A] [Group H] : Prop :=
  ∀ h : H,
    regularOrbit (hallFactor (A := A) (H := H)) (1, h) = hallBlock h

/-- A within-fiber transposition moves the natural Hall block partition. -/
def claim35741_blockTranspositionMoves : Prop :=
  ∀ (A H : Type*) [Group A] [Group H] [Fintype A] [Fintype H]
    [DecidableEq A] [DecidableEq H] [Nontrivial A] [Nontrivial H],
      blockTranspositionMoves (A := A) (H := H)

/-- The exact inverse-closed product Cayley graph has a characteristic Hall
factor whose regular orbit partition is moved by a graph automorphism. -/
def claim35743_characteristicHallOrbitPartitionMoved : Prop :=
  ∀ (A H : Type*) [Group A] [Group H] [Fintype A] [Fintype H]
    [DecidableEq A] [DecidableEq H] [Nontrivial A] [Nontrivial H],
    Nat.Coprime (Fintype.card A) (Fintype.card H) →
      connectionSetAdmissible (A := A) (H := H) ∧
      hallOrderCoprime (A := A) (H := H) ∧
      MathlibPlus.Open.ResearchFormalization.R1152.characteristicSubgroup
        (hallFactor (A := A) (H := H)) ∧
      regularHallOrbitPartition (A := A) (H := H) ∧
      blockTranspositionMoves (A := A) (H := H)

/-- The same complete-fiber graph moves the natural partition without using
coprimality; no Hall or characteristic conclusion is asserted in this scope. -/
def claim35746_unconditionalPartitionMove : Prop :=
  ∀ (A H : Type*) [Group A] [Group H] [Fintype A] [Fintype H]
    [DecidableEq A] [DecidableEq H] [Nontrivial A] [Nontrivial H],
      connectionSetAdmissible (A := A) (H := H) ∧
      regularHallOrbitPartition (A := A) (H := H) ∧
      blockTranspositionMoves (A := A) (H := H)

end

end MathlibPlus.Combinatorics.CayleyHallOrbitClaims
