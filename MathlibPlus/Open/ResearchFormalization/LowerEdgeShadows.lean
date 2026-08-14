import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- A spanning simple graph on the labelled vertex set `Fin n`, represented by its
finite set of two-element edges. -/
abbrev EdgeSet (n : ℕ) := Finset (Finset (Fin n))

def IsSimpleGraph {n : ℕ} (G : EdgeSet n) : Prop :=
  ∀ e ∈ G, e.card = 2

def Adj {n : ℕ} (G : EdgeSet n) (a b : Fin n) : Prop :=
  a ≠ b ∧ ({a, b} : Finset (Fin n)) ∈ G

def GraphIso {n : ℕ} (G H : EdgeSet n) : Prop :=
  ∃ p : Equiv.Perm (Fin n), ∀ a b : Fin n, Adj G a b ↔ Adj H (p a) (p b)

def UnlabeledClass {n : ℕ} (G : EdgeSet n) : Set (EdgeSet n) :=
  {H | IsSimpleGraph H ∧ GraphIso G H}

def EdgeSubsets (G : EdgeSet n) (j : ℕ) : Finset (EdgeSet n) :=
  G.powerset.filter (fun S => S.card = j)

def spanningLowerEdgeShadow (n j : ℕ) (G : EdgeSet n) :
    Multiset (Set (EdgeSet n)) :=
  (EdgeSubsets G j).val.map UnlabeledClass

def EdgeDeletionDeck (n : ℕ) (G : EdgeSet n) (k : ℕ) :
    Multiset (Set (EdgeSet n)) :=
  (EdgeSubsets G (G.card - k)).val.map UnlabeledClass

-- The definition above is the formal alignment for claim 20511.
/-- Equality of every lower shadow rank below `r` implies equality of the
full-multiplicity deck obtained by deleting `k = m-r+1` edges. -/
def claim_20512 : Prop :=
  ∀ (n m r : ℕ) (G H : EdgeSet n),
    IsSimpleGraph G →
    IsSimpleGraph H →
    G.card = m →
    H.card = m →
    ¬ GraphIso G H →
    (∀ j : ℕ, j < r →
      spanningLowerEdgeShadow n j G = spanningLowerEdgeShadow n j H) →
    EdgeDeletionDeck n G (m - r + 1) =
      EdgeDeletionDeck n H (m - r + 1)

end MathlibPlus.Open.ResearchFormalization
