import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Tree

open scoped BigOperators

noncomputable section

/-- The finite neighbor set and degree used in the tree claims. -/
noncomputable def treeNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (z : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => T.Adj z x)

def treeDegree {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (z : V) : ℕ :=
  (treeNeighbors T z).card

def leafOfTree {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (ell : V) : Prop :=
  treeDegree T ell = 1

/-- Adjacency in the card obtained by deleting a vertex. -/
def leafDeletionAdj {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (ell : V) (x y : {v // v ≠ ell}) : Prop :=
  T.Adj x.1 y.1

/-- Isomorphism of finite relational graphs, stated without relying on a named API. -/
def relationIso {V W : Type*}
    (AdjV : V → V → Prop) (AdjW : W → W → Prop) : Prop :=
  ∃ e : V ≃ W, ∀ x y, AdjV x y ↔ AdjW (e x) (e y)

def graphAutomorphism {V : Type*} (T : SimpleGraph V) (e : V ≃ V) : Prop :=
  ∀ x y, T.Adj x y ↔ T.Adj (e x) (e y)

def leafOrbit {V : Type*} (T : SimpleGraph V) (ell₁ ell₂ : V) : Prop :=
  ∃ e : V ≃ V, graphAutomorphism T e ∧ e ell₁ = ell₂

def neighborLoad {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (ell z : V) : ℕ :=
  ∑ x ∈ (treeNeighbors T z).erase ell, treeDegree T x - 1

/-- The support attachment jet in a leaf deletion card. -/
def attachmentJet {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (ell z : V) : ℕ × ℕ × ℕ × ℕ :=
  (1, treeDegree T z - 1, Nat.choose (treeDegree T z - 1) 2, neighborLoad T ell z)

/-- The second attachment jet has the displayed four coordinates. -/
def claim5683 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Prop :=
  T.IsTree →
    ∀ ell z, leafOfTree T ell → T.Adj ell z →
      attachmentJet T ell z =
        (1, treeDegree T z - 1, Nat.choose (treeDegree T z - 1) 2,
          ∑ x ∈ (treeNeighbors T z).erase ell, treeDegree T x - 1)

/-- Leaf deletion cards are classified by leaf automorphism orbits, with jet invariance. -/
def claim5685 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Prop :=
  T.IsTree →
    (∀ ell₁ ell₂,
      leafOfTree T ell₁ → leafOfTree T ell₂ →
        (relationIso (leafDeletionAdj T ell₁) (leafDeletionAdj T ell₂) ↔
          leafOrbit T ell₁ ell₂)) ∧
    (∀ ell₁ ell₂ z₁ z₂ e,
      leafOfTree T ell₁ → leafOfTree T ell₂ →
      T.Adj ell₁ z₁ → T.Adj ell₂ z₂ → graphAutomorphism T e →
      e ell₁ = ell₂ → e z₁ = z₂ →
      treeDegree T z₁ = treeDegree T z₂ ∧
      neighborLoad T ell₁ z₁ = neighborLoad T ell₂ z₂ ∧
      attachmentJet T ell₁ z₁ = attachmentJet T ell₂ z₂)

end

end MathlibPlus.Open.ResearchFormalization.Tree
