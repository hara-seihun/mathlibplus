import Mathlib

namespace MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges

noncomputable section

/-- The usual prime-power condition for the order of a finite field. -/
def IsPrimePower (q : ℕ) : Prop :=
  ∃ p e : ℕ, Nat.Prime p ∧ 0 < e ∧ q = p ^ e

/-- The lattice carrier of subspaces of the n-dimensional K-vector space. -/
abbrev SubspaceLattice (K : Type*) [Field K] (n : ℕ) :=
  Submodule K (Fin n → K)

/-- Edges of the subspace lattice, represented by their two endpoints. -/
abbrev SubspaceEdge (K : Type*) [Field K] (n : ℕ) :=
  {e : SubspaceLattice K n × SubspaceLattice K n //
    e.1 < e.2 ∧ Module.finrank K e.2 = Module.finrank K e.1 + 1}

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

noncomputable instance instFintypeSubspaceEdge : Fintype (SubspaceEdge K n) :=
  Fintype.ofFinite _

/-- The rank assigned to an edge by the dimension of its lower endpoint. -/
def edgeRank (e : SubspaceEdge K n) : ℕ := Module.finrank K e.1.1

/-- The simultaneous endpoint order on the edge poset. -/
def edgeLe (e f : SubspaceEdge K n) : Prop := e ≤ f

/-- The finite set of edges at a specified rank. -/
noncomputable def edgeRankSet (i : ℕ) : Finset (SubspaceEdge K n) :=
  (Finset.univ : Finset (SubspaceEdge K n)).filter (fun e => edgeRank e = i)

/-- The cardinality of the rank-i part of the edge poset. -/
noncomputable def edgeRankSize (K : Type*) [Field K] [Fintype K] (n i : ℕ) : ℕ :=
  (edgeRankSet (K := K) (n := n) i).card

/-- A standard recurrence definition of the Gaussian binomial coefficient. -/
def gaussianBinomial (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      gaussianBinomial q n k + q ^ (k + 1) * gaussianBinomial q n (k + 1)

/-- The edge-poset description for the lattice of subspaces of 𝔽_q^n. -/
def subspaceLatticeEdgePoset : Prop :=
  ∀ (q n : ℕ) (K : Type*) [Field K] [Fintype K],
    IsPrimePower q →
      Fintype.card K = q →
        (∀ e : SubspaceEdge K n, edgeRank e ∈ Finset.range n) ∧
          (∀ e f : SubspaceEdge K n,
            edgeLe e f ↔ e.1.1 ≤ f.1.1 ∧ e.1.2 ≤ f.1.2)

/-- The Gaussian rank-size formula and complementary-rank symmetry. -/
def symmetricRankSizeIdentity : Prop :=
  ∀ (q n i : ℕ) (K : Type*) [Field K] [Fintype K],
    IsPrimePower q →
      Fintype.card K = q →
        i < n →
          edgeRankSize K n i =
              gaussianBinomial q n i * gaussianBinomial q (n - i) 1 ∧
            gaussianBinomial q n i * gaussianBinomial q (n - i) 1 =
              gaussianBinomial q n (i + 1) * gaussianBinomial q (i + 1) 1 ∧
            edgeRankSize K n i = edgeRankSize K n (n - 1 - i)

end
end MathlibPlus.Open.Combinatorics.SubspaceLatticeEdges
