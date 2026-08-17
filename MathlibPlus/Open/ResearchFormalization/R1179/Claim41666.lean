import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1179.Claim41666

noncomputable section

/-- The complete part of the alternating connection set. -/
def thickConnection {A : Type*} {m : ℕ} [Group A] : Set (A × DihedralGroup m) :=
  (Set.univ : Set A) ×ˢ ({DihedralGroup.sr 0} : Set (DihedralGroup m))

/-- The single matching generator of the alternating connection set. -/
def thinConnection {A : Type*} {m : ℕ} [Group A] : Set (A × DihedralGroup m) :=
  {((1 : A), DihedralGroup.r 1 * DihedralGroup.sr 0)}

/-- Left multiplication using one element of a connection set. -/
def leftStep {M : Type*} [Mul M] (S : Set M) (x y : M) : Prop :=
  ∃ g ∈ S, g * x = y

/-- The alternating complete/matching Cayley graph. -/
def alternatingGraph {A : Type*} {m : ℕ} [Group A] :
    SimpleGraph (A × DihedralGroup m) :=
  SimpleGraph.fromRel
    (leftStep
      (thickConnection (A := A) (m := m) ∪
        thinConnection (A := A) (m := m)))

/-- The rotation fibres. -/
def rotationFiber {A : Type*} {m : ℕ} [Group A]
    (i : ZMod m) : Set (A × DihedralGroup m) :=
  {x | ∃ a : A, x = (a, DihedralGroup.r i)}

/-- The reflection fibres. -/
def reflectionFiber {A : Type*} {m : ℕ} [Group A]
    (i : ZMod m) : Set (A × DihedralGroup m) :=
  {x | ∃ a : A, x = (a, DihedralGroup.r i * DihedralGroup.sr 0)}

/-- An edge contributed from the complete part of the connection set. -/
def thickAdj {A : Type*} {m : ℕ} [Group A]
    (x y : A × DihedralGroup m) : Prop :=
  leftStep (thickConnection (A := A) (m := m)) x y ∨
    leftStep (thickConnection (A := A) (m := m)) y x

/-- An edge contributed from the matching part of the connection set. -/
def thinAdj {A : Type*} {m : ℕ} [Group A]
    (x y : A × DihedralGroup m) : Prop :=
  leftStep (thinConnection (A := A) (m := m)) x y ∨
    leftStep (thinConnection (A := A) (m := m)) y x

/-- Ordered intermediate vertices of a four-cycle through an ordered edge. -/
def fourCycleWitness {V : Type*} (Γ : SimpleGraph V) (x y : V) :=
  {p : V × V //
    p.1 ≠ x ∧ p.1 ≠ y ∧ p.2 ≠ x ∧ p.2 ≠ y ∧ p.1 ≠ p.2 ∧
      Γ.Adj x p.1 ∧ Γ.Adj p.1 p.2 ∧ Γ.Adj p.2 y ∧ Γ.Adj y x}

/-- The number of ordered intermediate-vertex representatives of a four-cycle. -/
def fourCycleCount {V : Type*} (Γ : SimpleGraph V) (x y : V) : ℕ :=
  Nat.card (fourCycleWitness Γ x y)

/-- Preservation of adjacency under a vertex permutation. -/
def graphAutomorphism {V : Type*} (Γ : SimpleGraph V)
    (e : Equiv.Perm V) : Prop :=
  ∀ x y, Γ.Adj x y ↔ Γ.Adj (e x) (e y)

/-- Equality of open neighbourhoods in the thick-edge subgraph. -/
def sameThickNeighborhood {A : Type*} {m : ℕ} [Group A]
    (x y : A × DihedralGroup m) : Prop :=
  ∀ z, thickAdj x z ↔ thickAdj y z

/-- Claim 41666: thick and thin edges have the exact four-cycle counts, graph
automorphisms preserve the two edge colours, and the thick-edge
neighbourhood classes recover the two indexed fibre families. -/
def claim41666 : Prop :=
  ∀ (A : Type*) [Group A] [Fintype A] [Nontrivial A] (m : ℕ),
    3 ≤ m →
    Nat.Coprime (Fintype.card A) (2 * m) →
    let n : ℕ := Fintype.card A
    (∀ x y : A × DihedralGroup m,
      thickAdj x y →
        fourCycleCount
          (alternatingGraph (A := A) (m := m)) x y = (n - 1) ^ 2) ∧
    (∀ x y : A × DihedralGroup m,
      thinAdj x y →
        fourCycleCount
          (alternatingGraph (A := A) (m := m)) x y = 0) ∧
    (∀ e : Equiv.Perm (A × DihedralGroup m),
      graphAutomorphism (alternatingGraph (A := A) (m := m)) e →
        ∀ x y, thickAdj x y ↔ thickAdj (e x) (e y)) ∧
    (∀ e : Equiv.Perm (A × DihedralGroup m),
      graphAutomorphism (alternatingGraph (A := A) (m := m)) e →
        ∀ x y, thinAdj x y ↔ thinAdj (e x) (e y)) ∧
    (∀ x y : A × DihedralGroup m,
      sameThickNeighborhood x y ↔
        ((∃ i : ZMod m,
            x ∈ rotationFiber i ∧ y ∈ rotationFiber i) ∨
          (∃ i : ZMod m,
            x ∈ reflectionFiber i ∧ y ∈ reflectionFiber i))) ∧
    (∀ x : A × DihedralGroup m,
      (∃! i : ZMod m, x ∈ rotationFiber i) ∨
        (∃! i : ZMod m, x ∈ reflectionFiber i))

end

end MathlibPlus.Open.ResearchFormalization.R1179.Claim41666
