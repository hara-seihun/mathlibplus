import MathlibPlus.GraphTheory.Claim28295
import Mathlib

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The component-size polynomial evaluated at a sequence of coefficients.  The
sum is over all edge subsets of the finite graph, and every component of the
spanning subgraph contributes the coefficient indexed by its cardinality. -/
def componentSizeEvaluation
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {R : Type*} [CommSemiring R]
    (x : ℕ → R) : R :=
  ∑ A : Finset (Sym2 V),
    if (A : Set (Sym2 V)) ⊆ H.edgeSet then
      (Multiset.map x
        (MathlibPlus.GraphTheory.Claim28295.componentSizes
          (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))))).prod
    else 0

/-- The weight of a three-colouring in the three-colour random-cluster
expansion. -/
def threeColorWeight
    {V : Type*} [Fintype V] (σ : V → Fin 3)
    {R : Type*} [CommSemiring R] (a b c : R) : R :=
  a ^ (Finset.univ.filter (fun v => σ v = (0 : Fin 3))).card *
    b ^ (Finset.univ.filter (fun v => σ v = (1 : Fin 3))).card *
    c ^ (Finset.univ.filter (fun v => σ v = (2 : Fin 3))).card

/-- The number of monochromatic edges, computed from the two orientations of
an edge and divided by two. -/
def monochromaticEdgeCount
    {V : Type*} [Fintype V] (H : SimpleGraph V) (σ : V → Fin 3) : ℕ :=
  (Finset.univ.filter
    (fun p : V × V => H.Adj p.1 p.2 ∧ σ p.1 = σ p.2)).card / 2

/-- The exact finite-tree specialization and colouring expansion of the
three-colour component-size polynomial. -/
def threeColorRandomClusterSpecialization : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (H : SimpleGraph V), H.IsTree →
    ∀ (R : Type*) [Field R] (a b c t : R), t ≠ 0 →
      t ^ Fintype.card V *
          componentSizeEvaluation H (fun k => (a ^ k + b ^ k + c ^ k) / t) =
        ∑ σ : V → Fin 3,
          threeColorWeight σ a b c *
            (1 + t) ^ monochromaticEdgeCount H σ

end

end MathlibPlus.Open.Combinatorics
