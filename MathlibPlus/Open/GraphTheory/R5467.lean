import Mathlib

namespace MathlibPlus.Open.GraphTheory.R5467

/-- The adjacency-refined profile of an unordered pair, with the endpoint
 degrees sorted and the common-neighbour count retained. -/
structure PairProfile where
  adj : Prop
  r : ℕ
  s : ℕ
  c : ℕ

/-- The profile attached to two distinct vertices of a finite simple graph. -/
noncomputable def pairProfile {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) : PairProfile := by
  classical
  exact {
    adj := G.Adj u v
    r := min (G.neighborFinset u).card (G.neighborFinset v).card
    s := max (G.neighborFinset u).card (G.neighborFinset v).card
    c := (G.neighborFinset u ∩ G.neighborFinset v).card
  }

/-- A quadruple is a profile value of `G` when it occurs on a distinct pair. -/
def profileValue {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : PairProfile) : Prop :=
  ∃ u v : V, u ≠ v ∧ pairProfile G u v = x

/-- The exact integer transfer predicate for two distinct same-adjacency
 profile values and an attachment-count pair. -/
def attachmentTransfer (x y : PairProfile) (p q : Fin 3) : Prop :=
  x ≠ y ∧
    (x.adj ↔ y.adj) ∧
    ∃ d₁ d₂ : ℕ,
      ((d₁ = x.r ∧ d₂ = x.s) ∨ (d₁ = x.s ∧ d₂ = x.r)) ∧
      ∃ a₁ a₂ b₁ b₂ : Fin 2,
        ({(y.r : ℤ), (y.s : ℤ)} : Multiset ℤ) =
            ({(d₁ : ℤ) + (b₁.val : ℤ) - (a₁.val : ℤ),
              (d₂ : ℤ) + (b₂.val : ℤ) - (a₂.val : ℤ)} : Multiset ℤ) ∧
        (y.c : ℤ) - (x.c : ℤ) =
          (b₁.val : ℤ) * (b₂.val : ℤ) -
            (a₁.val : ℤ) * (a₂.val : ℤ) ∧
        p.val = a₁.val + a₂.val ∧
        q.val = b₁.val + b₂.val ∧
        p ≠ q

/-- A transfer type is realized by two profile values from either
 same-adjacency layer of `G`. -/
def realizedTransfer {V : Type*} [Fintype V]
    (G : SimpleGraph V) (p q : Fin 3) : Prop :=
  ∃ x y : PairProfile,
    profileValue G x ∧ profileValue G y ∧ attachmentTransfer x y p q

/-- The three-state transfer graph `A(G)`. -/
def attachmentGraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (realizedTransfer G)

/-- The exact edge description of the transfer graph in R-5467.2. -/
def claim_55231 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
    3 ≤ Fintype.card V →
      ∀ p q : Fin 3,
        (attachmentGraph G).Adj p q ↔
          p ≠ q ∧
            (realizedTransfer G p q ∨ realizedTransfer G q p)

/-- The row `e_p-e_q`, with a fixed orientation for an unordered pair. -/
def incidenceRow (p q : Fin 3) : Fin 3 → ℚ :=
  fun i => if i = p then 1 else if i = q then -1 else 0

/-- A list is a complete list of realized unordered transfer types.  The
 first conjunct permits repetitions, while the second ensures that every
 realized unordered type contributes a row. -/
def CompleteTransferRows {V : Type*} [Fintype V]
    (G : SimpleGraph V) (rows : List (Fin 3 × Fin 3)) : Prop :=
  (∀ e, e ∈ rows →
    e.1 < e.2 ∧ (attachmentGraph G).Adj e.1 e.2) ∧
    (∀ p q : Fin 3,
      p < q → (attachmentGraph G).Adj p q → (p, q) ∈ rows)

/-- The rational matrix whose rows are exactly the supplied realized transfer
 types; no rows for nonedges are present. -/
def transferMatrix (rows : List (Fin 3 × Fin 3)) :
    Matrix (Fin rows.length) (Fin 3) ℚ :=
  fun i j => incidenceRow (rows.get i).1 (rows.get i).2 j

/-- Disconnectedness of a graph on the three attachment states. -/
def GraphDisconnected (A : SimpleGraph (Fin 3)) : Prop :=
  ∃ p q : Fin 3, ¬ A.Reachable p q

/--
R-5467.3 (claim 55232): for every complete list of the realized unordered
 transfer types (with repetitions allowed), the rational incidence matrix
 has rank `3 - #components(A(G))`, and the stipulated disconnectedness/rank
 equivalence is explicit.
-/
def claim_55232 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
    3 ≤ Fintype.card V →
      ∀ rows : List (Fin 3 × Fin 3),
        CompleteTransferRows G rows →
          Matrix.rank (transferMatrix rows) =
              3 - Fintype.card (attachmentGraph G).ConnectedComponent ∧
            (GraphDisconnected (attachmentGraph G) ↔
              Matrix.rank (transferMatrix rows) ≤ 1)

end MathlibPlus.Open.GraphTheory.R5467
