import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffee2

noncomputable section
open scoped Classical

/-- A clique in a finite simple graph. -/
def graphClique {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ s → w ∈ s → v ≠ w → G.Adj v w

/-- An independent set in a finite simple graph. -/
def graphIndependent {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ s → w ∈ s → ¬G.Adj v w

/-- A proper coloring, with colors allowed to have empty fibers. -/
def properGraphColoring {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

/-- Every color class is homogeneous, i.e. a clique or an independent set. -/
def homogeneousGraphColoring {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    graphClique G {v : V | c v = i} ∨
      graphIndependent G {v : V | c v = i}

/-- Every color class is independent and has cardinality at most `a`. -/
def boundedIndependentColoring {V : Type*} (G : SimpleGraph V) (a k : ℕ)
    (c : V → Fin k) : Prop :=
  (∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w) ∧
    ∀ i : Fin k, Set.ncard {v : V | c v = i} ≤ a

/-- The least natural number satisfying a predicate, with a harmless empty fallback. -/
def leastNatural (p : ℕ → Prop) : ℕ :=
  if h : ∃ k, p k then Nat.find h else 0

/-- Chromatic number as the least number of independent color classes. -/
def graphChromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  leastNatural (fun k => ∃ c : V → Fin k, properGraphColoring G c)

/-- The cocoloring number as the least number of homogeneous color classes. -/
def graphZeta {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  leastNatural (fun k => ∃ c : V → Fin k, homogeneousGraphColoring G c)

/-- The bounded chromatic surrogate from the admitted statement. -/
def graphChromaticAtMost {V : Type*} [Fintype V] (G : SimpleGraph V) (a : ℕ) : ℕ :=
  leastNatural (fun k => ∃ c : V → Fin k, boundedIndependentColoring G a k c)

/-- The two gaps named in the admitted statement. -/
def graphGap {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  graphChromaticNumber G - graphZeta G

def graphBoundedGap {V : Type*} [Fintype V] (G : SimpleGraph V) (a : ℕ) : ℕ :=
  graphChromaticAtMost G a - graphZeta G

/-- The finite optimization value over all vertex subsets. -/
def graphZetaOptimizationValue {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {
    n : ℕ |
      ∃ S : Finset V,
        n =
          graphChromaticNumber
              (G.induce (↑((Finset.univ : Finset V) \ S) : Set V)) +
            graphChromaticNumber ((Gᶜ).induce (↑S : Set V))
  }

/-- Claim 44090: the exact finite optimization identity for every finite graph. -/
def claim44090_zeta_optimization_identity {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  graphZeta G = graphZetaOptimizationValue G

/-- The direct relation underlying the Cayley graph in claim 44220. -/
def hallConnectionSet {A H : Type*} [Group A] [Group H] : Set (A × H) :=
  {g : A × H | g.1 ≠ (1 : A)}

/-- The complete-multipartite Cayley graph from
`(A \ {1_A}) × H`. -/
def completeMultipartiteCayleyGraph {A H : Type*} [Group A] [Group H] :
    SimpleGraph (A × H) :=
  SimpleGraph.fromRel (fun x y : A × H => x⁻¹ * y ∈ hallConnectionSet)

/-- A permutation is a graph automorphism when it preserves adjacency in both directions. -/
def graphPermutationAutomorphism {V : Type*} (G : SimpleGraph V) (e : Equiv.Perm V) : Prop :=
  ∀ x y : V, G.Adj x y ↔ G.Adj (e x) (e y)

/-- The natural Hall-`A` block indexed by `h`. -/
def naturalHallBlock {A H : Type*} (h : H) : Set (A × H) :=
  {x : A × H | x.2 = h}

/-- The image of one natural block meets both blocks named in the swap. -/
def crossesNaturalHallBlocks {A H : Type*} (e : Equiv.Perm (A × H))
    (h₁ h₂ : H) : Prop :=
  (∃ x : A × H, x ∈ e '' naturalHallBlock h₁ ∧ x.2 = h₁) ∧
    (∃ x : A × H, x ∈ e '' naturalHallBlock h₁ ∧ x.2 = h₂) ∧
    e '' naturalHallBlock h₁ ≠ naturalHallBlock h₁ ∧
    e '' naturalHallBlock h₁ ≠ naturalHallBlock h₂

/-- Claim 44220: a within-part transposition is a graph automorphism and moves a
natural Hall block across the two natural blocks. -/
def claim44220_hall_block_swap
    (A H : Type*) [Group A] [Group H] [Fintype A] [Fintype H] [Nontrivial A] : Prop :=
  SimpleGraph.Connected (completeMultipartiteCayleyGraph (A := A) (H := H)) ∧
    ∀ (a₀ : A) (h₁ h₂ : H), h₁ ≠ h₂ →
      let e : Equiv.Perm (A × H) := Equiv.swap (a₀, h₁) (a₀, h₂)
      graphPermutationAutomorphism
          (completeMultipartiteCayleyGraph (A := A) (H := H)) e ∧
        crossesNaturalHallBlocks e h₁ h₂

end
end MathlibPlus.Open.ResearchFormalization.Batch019ffee2
