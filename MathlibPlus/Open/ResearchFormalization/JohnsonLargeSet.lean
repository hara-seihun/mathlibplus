import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.JohnsonLargeSet

open scoped BigOperators

abbrev JohnsonVertex (k : ℕ) := {s : Finset (Fin (2 * k)) // s.card = k}

/-- Adjacency in the Johnson graph `J(2k,k)`. -/
def johnsonAdjacent (k : ℕ) (A B : JohnsonVertex k) : Prop :=
  A.1 ≠ B.1 ∧ (A.1 ∩ B.1).card = k - 1

/-- A proper coloring of the Johnson graph by `k+1` colors. -/
def properJohnsonColoring (k : ℕ)
    (coloring : JohnsonVertex k → Fin (k + 1)) : Prop :=
  ∀ ⦃A B : JohnsonVertex k⦄,
    johnsonAdjacent k A B → coloring A ≠ coloring B

/-- A large set of `S(r,k,n)` systems, with all blocks explicitly represented. -/
def largeSet (r k n : ℕ) : Prop :=
  ∃ classes : Fin (k + 1) → Finset (Finset (Fin n)),
    (∀ c : Fin (k + 1), ∀ B ∈ classes c, B.card = k) ∧
    (∀ B : Finset (Fin n), B.card = k →
      ∃! c : Fin (k + 1), B ∈ classes c) ∧
    (∀ c : Fin (k + 1), ∀ T : Finset (Fin n), T.card = r →
      ∃! B : Finset (Fin n), B ∈ classes c ∧ T ⊆ B)

/-- The exact-one extension property used in the coloring-to-large-set direction. -/
def coloringExtensionExactlyOne (k : ℕ)
    (coloring : JohnsonVertex k → Fin (k + 1)) : Prop :=
  ∀ color : Fin (k + 1), ∀ T : Finset (Fin (2 * k)),
    T.card = k - 1 →
      ∃! x : Fin (2 * k),
        x ∉ T ∧
          ∃ hcard : (T ∪ {x}).card = k,
            coloring ⟨T ∪ {x}, hcard⟩ = color

/-- The Johnson-coloring/large-set equivalence and its exact extension clause. -/
def claim46301 : Prop :=
  ∀ k : ℕ,
    ((∃ coloring : JohnsonVertex k → Fin (k + 1),
        properJohnsonColoring k coloring) ↔
      largeSet (k - 1) k (2 * k)) ∧
      (∀ coloring : JohnsonVertex k → Fin (k + 1),
        properJohnsonColoring k coloring →
          coloringExtensionExactlyOne k coloring)

end MathlibPlus.Open.ResearchFormalization.JohnsonLargeSet
