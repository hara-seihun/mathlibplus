import Mathlib
import MathlibPlus.Combinatorics.Claim44521

namespace MathlibPlus.Open.ResearchFormalization.Claim16006

open scoped Classical BigOperators

noncomputable section

private abbrev GraphType (n : ℕ) :=
  MathlibPlus.Combinatorics.Claim44521.finiteSimpleGraphType n

private def graphRepresentative {n : ℕ} (G : GraphType n) : SimpleGraph (Fin n) :=
  Quotient.out G

private def deletedVertexGraph {m : ℕ} (G : SimpleGraph (Fin (m + 1)))
    (v : Fin (m + 1)) : SimpleGraph (Fin m) :=
  G.comap v.succAbove

private def cardMultiplicity (F : GraphType m) (G : GraphType (m + 1)) : ℕ :=
  Nat.card {v : Fin (m + 1) //
    MathlibPlus.Combinatorics.Claim44521.graphTypeOf m
      (deletedVertexGraph (graphRepresentative G) v) = F}

private def fallingQuadraticRow (F H : GraphType m) : GraphType (m + 1) → ℚ :=
  letI : DecidableEq (GraphType m) := Classical.decEq _
  fun G =>
    if F = H then
      (cardMultiplicity F G : ℚ) *
        ((cardMultiplicity F G - 1 : ℕ) : ℚ)
    else
      (cardMultiplicity F G : ℚ) * (cardMultiplicity H G : ℚ)

private def graphEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.card {e : Sym2 (Fin n) // e ∈ G.edgeSet}

private def graphAutCard {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.card {e : Equiv.Perm (Fin n) //
    ∀ u v, G.Adj u v ↔ G.Adj (e u) (e v)}

private def graphWeight {n : ℕ} (G : GraphType n) : ℚ :=
  let X := graphRepresentative G
  (-1 : ℚ) ^ graphEdgeCount X * (Nat.factorial n : ℚ) /
    (graphAutCard X : ℚ)

private abbrev Partition (n : ℕ) := Finset (Finset (GraphType n))

private def isPartition (P : Partition n) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
    (∀ B ∈ P, ∀ D ∈ P, B ≠ D → Disjoint B D) ∧
      (∀ X : GraphType n, ∃ B ∈ P, X ∈ B)

private def blockMass (r : GraphType (n + 1) → ℚ)
    (B : Finset (GraphType (n + 1))) : ℚ :=
  ∑ X ∈ B, graphWeight X * r X

private def binaryOn (r : GraphType (n + 1) → ℚ) (P : Partition (n + 1)) : Prop :=
  ∃ B D, B ∈ P ∧ D ∈ P ∧ B ≠ D ∧
    blockMass r B ≠ 0 ∧ blockMass r D ≠ 0 ∧
      ∀ E ∈ P, E ≠ B → E ≠ D → blockMass r E = 0

/-- Claim 16006: a repeated-card falling row is binary at a giant block and a
residual singleton, with the stated nonzero singleton mass. -/
def claim16006 : Prop :=
  ∀ (n : ℕ) (P : Partition (n + 1))
      (C : Finset (GraphType (n + 1)))
      (G : GraphType (n + 1)) (F : GraphType n),
    isPartition P →
    C ∈ P →
    ({G} : Finset (GraphType (n + 1))) ∈ P →
    (∀ B ∈ P, B = C ∨ B.card = 1) →
    1 < C.card →
    G ∉ C →
    2 ≤ cardMultiplicity F G →
    (∀ B ∈ P,
      B ≠ C →
      B ≠ ({G} : Finset (GraphType (n + 1))) →
      blockMass (fallingQuadraticRow F F) B = 0) →
    binaryOn (fallingQuadraticRow F F) P ∧
      blockMass (fallingQuadraticRow F F) ({G} : Finset (GraphType (n + 1))) =
        graphWeight G * (cardMultiplicity F G : ℚ) *
          ((cardMultiplicity F G - 1 : ℕ) : ℚ) ∧
      graphWeight G * (cardMultiplicity F G : ℚ) *
          ((cardMultiplicity F G - 1 : ℕ) : ℚ) ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.Claim16006
