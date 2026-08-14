import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- Twice-counted finite edge sums give the edge count of an induced vertex set. -/
def inducedEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V) : ℕ := by
  classical
  exact (∑ x : V, ∑ y : V,
    if x ∈ S ∧ y ∈ S ∧ G.Adj x y then 1 else 0) / 2

def graphNeighborhood {V : Type*} (G : SimpleGraph V) (v : V) : Set V :=
  {u | G.Adj v u}

/-- The neighborhood/non-neighborhood edge relation for an 18-regular graph of order 43. -/
def localNeighborhoodNonneighborhoodEdgeRelation : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = 43 →
    (∀ v : V, Nat.card {u : V // G.Adj v u} = 18) →
    ∀ v : V,
      ((inducedEdgeCount G ((graphNeighborhood G v)ᶜ \ {v}) : ℤ) -
        (inducedEdgeCount G (graphNeighborhood G v) : ℤ)) = 63

/-- A four-clique and a triangle are expressed directly in the adjacency relation. -/
def hasFourClique {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧
    G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

def isK4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ hasFourClique G

def neighborhoodIsTriangleFree {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ a b c : V,
    a ∈ graphNeighborhood G v →
    b ∈ graphNeighborhood G v →
    c ∈ graphNeighborhood G v →
    a ≠ b → a ≠ c → b ≠ c →
    ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c)

def isTriangle {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  s.card = 3 ∧
    ∀ ⦃x y : V⦄, x ∈ s → y ∈ s → x ≠ y → G.Adj x y

def triangleCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  Nat.card {s : Finset V // isTriangle G s}

/-- The K₄-free neighborhood argument and its Mantel inequality. -/
def mantelNeighborhoodInequality : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (P : SimpleGraph V),
    Fintype.card V = 18 →
    isK4Free P →
    ∀ (a : V → ℕ),
      (∀ i : V, a i = Nat.card {j : V // P.Adj i j}) →
      (∀ v : V, neighborhoodIsTriangleFree P v) ∧
        3 * triangleCount P ≤ ∑ i : V, (a i ^ 2 / 4)

/-- Homogeneous modules under modular decomposition. -/
def isHomogeneousModule {V : Type*} (G : SimpleGraph V) (M : Set V) : Prop :=
  ∀ v : V, v ∉ M →
    ((∀ x : V, x ∈ M → G.Adj v x) ∨
      (∀ x : V, x ∈ M → ¬ G.Adj v x))

/-- Prime graphs have only the empty set, singletons, and the whole vertex set as modules. -/
def isPrimeUnderModularDecomposition {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ M : Set V, isHomogeneousModule G M →
    M = ∅ ∨ (∃ v : V, M = ({v} : Set V)) ∨ M = Set.univ

end MathlibPlus.Open.ResearchFormalization
