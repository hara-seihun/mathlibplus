import Mathlib

namespace MathlibPlus.Open.GraphTheory.CayleyAtlas

noncomputable section

/-- Finite identity-free inverse-closed connection sets. -/
def IsConnectionSet {G : Type*} [DecidableEq G] [Fintype G] [Group G]
    (k : ℕ) (S : Finset G) : Prop :=
  1 ∉ S ∧ (∀ x ∈ S, x⁻¹ ∈ S) ∧ S.card = k

def connectionSetType (G : Type*) [DecidableEq G] [Fintype G] [Group G]
    (k : ℕ) := {S : Finset G // IsConnectionSet k S}

def ordinaryCayleyGraph {G : Type*} [Group G]
    (S : Finset G) : SimpleGraph G := SimpleGraph.mulCayley (S : Set G)

def GraphIsomorphic {G : Type*} [Group G]
    (S T : Finset G) : Prop :=
  Nonempty (ordinaryCayleyGraph S ≃g ordinaryCayleyGraph T)

def automorphismImage {G : Type*} [DecidableEq G] [Group G]
    (α : G ≃* G) (S : Finset G) : Finset G := S.image α

def IsCIRow {G : Type*} [DecidableEq G] [Fintype G] [Group G]
    (k : ℕ) : Prop :=
  ∀ S T : Finset G, IsConnectionSet k S → IsConnectionSet k T →
    GraphIsomorphic S T → ∃ α : G ≃* G, automorphismImage α S = T

/-- A finite representative set for the full-automorphism orbit relation. -/
def HasAutOrbitCount {G : Type*} [DecidableEq G] [Fintype G] [Group G]
    (k c : ℕ) : Prop :=
  ∃ R : Finset (Finset G),
    R.card = c ∧
    (∀ S, IsConnectionSet k S →
      ∃ T ∈ R, IsConnectionSet k T ∧
        ∃ α : G ≃* G, automorphismImage α S = T) ∧
    (∀ S ∈ R, IsConnectionSet k S) ∧
    (∀ S ∈ R, ∀ T ∈ R,
      (∃ α : G ≃* G, automorphismImage α S = T) → S = T)

/-- A finite representative set for graph-isomorphism types of the same atlas row. -/
def HasGraphTypeCount {G : Type*} [DecidableEq G] [Fintype G] [Group G]
    (k c : ℕ) : Prop :=
  ∃ R : Finset (Finset G),
    R.card = c ∧
    (∀ S, IsConnectionSet k S →
      ∃ T ∈ R, IsConnectionSet k T ∧ GraphIsomorphic S T) ∧
    (∀ S ∈ R, IsConnectionSet k S) ∧
    (∀ S ∈ R, ∀ T ∈ R,
      GraphIsomorphic S T → S = T)

/-- Complement inside the nonidentity elements. -/
def connectionComplement {G : Type*} [DecidableEq G] [Fintype G] [Group G]
    (S : Finset G) : Finset G := (Finset.univ.erase (1 : G)) \ S

/-- The complement-transfer assertion used by both admitted Cayley packets. -/
def ComplementTransportStatement
    (G : Type*) [DecidableEq G] [Fintype G] [Group G]
    (high : ℕ) (lowRows : Set ℕ) : Prop :=
  ∀ k : ℕ, k ∈ lowRows →
    (∀ S : Finset G, IsConnectionSet k S →
      (connectionComplement S).card = high - k ∧
      IsConnectionSet (high - k) (connectionComplement S) ∧
      (∀ α : G ≃* G,
        automorphismImage α (connectionComplement S) =
          connectionComplement (automorphismImage α S))) ∧
    (∀ S T : Finset G,
      IsConnectionSet k S → IsConnectionSet k T →
      (GraphIsomorphic S T ↔
        GraphIsomorphic (connectionComplement S) (connectionComplement T))) ∧
    (IsCIRow (G := G) k → IsCIRow (G := G) (high - k))

/-- Claim 32825: the exact low-valency CI atlas on `Q₂₂₀`. -/
def lowValencyExactCIAtlas_claim32825 : Prop :=
  let G := QuaternionGroup 55
  Nat.card G = 220 ∧
  IsCIRow (G := G) 1 ∧ IsCIRow (G := G) 2 ∧
  IsCIRow (G := G) 3 ∧ IsCIRow (G := G) 4 ∧
  IsCIRow (G := G) 5 ∧ IsCIRow (G := G) 6 ∧
  Nat.card {S : Finset G // IsConnectionSet 1 S} = 1 ∧
  Nat.card {S : Finset G // IsConnectionSet 2 S} = 109 ∧
  Nat.card {S : Finset G // IsConnectionSet 3 S} = 109 ∧
  Nat.card {S : Finset G // IsConnectionSet 4 S} = 5886 ∧
  Nat.card {S : Finset G // IsConnectionSet 5 S} = 5886 ∧
  Nat.card {S : Finset G // IsConnectionSet 6 S} = 209934 ∧
  HasAutOrbitCount (G := G) 1 1 ∧ HasAutOrbitCount (G := G) 2 7 ∧
  HasAutOrbitCount (G := G) 3 7 ∧ HasAutOrbitCount (G := G) 4 94 ∧
  HasAutOrbitCount (G := G) 5 94 ∧ HasAutOrbitCount (G := G) 6 1475 ∧
  HasGraphTypeCount (G := G) 1 1 ∧ HasGraphTypeCount (G := G) 2 7 ∧
  HasGraphTypeCount (G := G) 3 7 ∧ HasGraphTypeCount (G := G) 4 94 ∧
  HasGraphTypeCount (G := G) 5 94 ∧ HasGraphTypeCount (G := G) 6 1475

/-- Claim 32827: complement transport for the `Q₂₂₀` low rows. -/
def complementTransportQ220_claim32827 : Prop :=
  let G := QuaternionGroup 55
  Nat.card G = 220 ∧
    ComplementTransportStatement G 219 ({1, 2, 3, 4, 5, 6} : Set ℕ)

/-- Claim 32832: the fixed-valency rows on `C₃² × D₁₀` have no atlas defect. -/
def exactFixedValencyAtlas_claim32832 : Prop :=
  let G := Multiplicative (Fin 2 → ZMod 3) × DihedralGroup 5
  Nat.card G = 90 ∧
  ∀ k : ℕ, k ∈ ({14, 15, 16, 17, 18, 19, 20} : Set ℕ) →
    IsCIRow (G := G) k ∧
    HasAutOrbitCount (G := G) k (Nat.card {S : Finset G // IsConnectionSet k S}) ∧
    HasGraphTypeCount (G := G) k (Nat.card {S : Finset G // IsConnectionSet k S})

/-- Claim 32834: complement transport for the rows 14--20. -/
def complementTransportC3SquareD10_claim32834 : Prop :=
  let G := Multiplicative (Fin 2 → ZMod 3) × DihedralGroup 5
  Nat.card G = 90 ∧
    ComplementTransportStatement G 89 ({14, 15, 16, 17, 18, 19, 20} : Set ℕ)

end
end MathlibPlus.Open.GraphTheory.CayleyAtlas
