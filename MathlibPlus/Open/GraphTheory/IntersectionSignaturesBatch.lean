import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory

noncomputable section
open Classical

/-- Common-neighborhood intersection of a finite set of vertices. -/
def commonNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun w => ∀ v ∈ S, G.Adj v w)

def iteratedCommonNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ → Finset V → Finset V
  | 0, S => S
  | k + 1, S => commonNeighborhood G (iteratedCommonNeighborhood G k S)

def graphIntersectionSignature {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ} (t : Fin r → V) : Set ℕ :=
  {q | ∃ (S : Finset (Fin r)) (k : ℕ),
    q = (iteratedCommonNeighborhood G k (S.image t)).card}

def graphAutomorphism {V : Type*} (G : SimpleGraph V) (e : V ≃ V) : Prop :=
  ∀ x y, G.Adj x y ↔ G.Adj (e x) (e y)

/-- Claim 42479: the complete tuple intersection signature, including all
iterations of common-neighborhood intersections, is graph-automorphism
invariant. -/
def claim42479_complete_intersection_signature : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ)
    (G : SimpleGraph V) (t : Fin r → V) (e : V ≃ V),
    graphAutomorphism G e →
      graphIntersectionSignature G t =
        graphIntersectionSignature G (fun i => e (t i))

/-- A permutation subgroup acts regularly on a finite vertex set. -/
def regularPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (A : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! g : A, g.1 x = y

abbrev modelC2rC9 (r : ℕ) :=
  Multiplicative (Fin r → ZMod 2) × Multiplicative (ZMod 9)

def conjugatePermutationSubgroups {Ω : Type*}
    (A B : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ g : Equiv.Perm Ω, ∀ x,
    x ∈ B ↔ ∃ y, y ∈ A ∧ x = g * y * g⁻¹

def invariantBlock {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) (B : Finset Ω) : Prop :=
  B.Nonempty ∧
    ∀ g : G, B.image g.1 = B ∨ Disjoint (B.image g.1) B

def primitivePermutationGroup {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ¬ ∃ B : Finset Ω, invariantBlock G B ∧
    1 < B.card ∧ B.card < Fintype.card Ω

def minimalNontrivialBlock {Ω : Type*} [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) (B : Finset Ω) : Prop :=
  invariantBlock G B ∧ 1 < B.card ∧ B.card < Fintype.card Ω ∧
    ∀ C : Finset Ω, invariantBlock G C → 1 < C.card → B.card ≤ C.card

/-- Claim 42481: in the primitive case the generated action gives conjugacy of
regular copies; a residual nonconjugate pair has a minimal nontrivial block. -/
def claim42481_primitive_generated_actions : Prop :=
  ∀ (r : ℕ) (hr : r = 3 ∨ r = 4 ∨ r = 5)
    (Ω : Type*) [Fintype Ω]
    (A B : Subgroup (Equiv.Perm Ω)),
    regularPermutationSubgroup A → regularPermutationSubgroup B →
      Nonempty (modelC2rC9 r ≃* A) →
      Nonempty (modelC2rC9 r ≃* B) →
      let G := Subgroup.closure (A.carrier ∪ B.carrier)
      (primitivePermutationGroup G → conjugatePermutationSubgroups A B) ∧
        (¬ conjugatePermutationSubgroups A B →
          ∃ C : Finset Ω, minimalNontrivialBlock G C)

/-- Set-theoretic cells for the binary coordinate and C9 quotient partitions. -/
def binaryCosetPartition (r : ℕ) (j : Fin r) : Set (Set ((Fin r → ZMod 2) × ZMod 9)) :=
  {C | ∃ a : ZMod 2, C = {x | x.1 j = a}}

def c9CosetPartition (r : ℕ) : Set (Set ((Fin r → ZMod 2) × ZMod 9)) :=
  {C | ∃ a : ZMod 9, C = {x | x.2 = a}}

def setCommonNeighborhood {V : Type*} (G : SimpleGraph V) (C : Set V) : Set V :=
  {w | ∀ v ∈ C, G.Adj v w}

def iteratedSetCommonNeighborhood {V : Type*} (G : SimpleGraph V) :
    ℕ → Set V → Set V
  | 0, C => C
  | k + 1, C =>
      setCommonNeighborhood G (iteratedSetCommonNeighborhood G k C)

def cellIntersectionSignature {V : Type*} [Fintype V]
    (G : SimpleGraph V) (P : Set (Set V)) : Set (ℕ × ℕ) :=
  {q | ∃ C ∈ P, ∃ k : ℕ,
    q = (Fintype.card {x : V // x ∈ C},
      Fintype.card {x : V // x ∈ iteratedSetCommonNeighborhood G k C})}

/-- Claim 42484: even complete-graph low-order data (and hence its iterated
intersection signature) cannot by itself reconstruct a distinguished binary
coset partition. -/
def claim42484_low_order_signature_failure : Prop :=
  ∀ (r : ℕ), r ≥ 3 →
    ∃ j₀ j₁ : Fin r,
      j₀.val = 0 ∧ j₁.val = 1 ∧ j₀ ≠ j₁ ∧
        let V := (Fin r → ZMod 2) × ZMod 9
        let G : SimpleGraph V := ⊤
        let P₀ := binaryCosetPartition r j₀
        let P₁ := binaryCosetPartition r j₁
        let P₉ := c9CosetPartition r
        P₀ ≠ P₁ ∧ P₀ ≠ P₉ ∧
          cellIntersectionSignature G P₀ = cellIntersectionSignature G P₁

end
end MathlibPlus.Open.GraphTheory
