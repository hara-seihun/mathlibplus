import MathlibPlus.Open.ResearchFormalization.R0523Claim22338

namespace MathlibPlus.Open.ResearchFormalization.R0523Claim22328

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0523Claim22338

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ForestVertex (d : ℕ) (V : Fin d → Type*) := Σ i, V i

/-- The disjoint union graph of the component graphs. -/
def forestGraph {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i)) :
    SimpleGraph (ForestVertex d V) :=
  SimpleGraph.fromRel (fun x y =>
    ∃ h : x.1 = y.1, (B x.1).Adj x.2 (cast (congrArg V h.symm) y.2))

/-- The roots of the disjoint rooted forest. -/
def forestRoots {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (r : ∀ i : Fin d, V i) : Finset (ForestVertex d V) :=
  (Finset.univ : Finset (ForestVertex d V)).filter (fun x => x.2 = r x.1)

/-- The product of the shifted rooted component factors. -/
def rootedForestProduct {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i)) (r : ∀ i : Fin d, V i) :
    ShiftedPolynomial :=
  ∏ i : Fin d, shiftedRootedFactor (B i) (r i)

/-- The independent-deletion sum for the disjoint rooted forest. -/
def independentDeletionTransform {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i)) (r : ∀ i : Fin d, V i) :
    ShiftedPolynomial :=
  ∑ I ∈ ((Finset.univ : Finset (ForestVertex d V)).powerset).filter (fun I =>
      independentVertexSet (forestGraph V B) I ∧
        (I ∩ forestRoots V r).card = 0),
    (-MvPolynomial.X none) ^ I.card *
      renameUToY (deletedUPolynomial (forestGraph V B) I)

/-- Claim 22328 for arbitrary finite disjoint rooted forests, including the
empty forest and components of different cardinalities. -/
def claim22328 : Prop :=
  ∀ {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i))
    (r : ∀ i : Fin d, V i),
    (∀ i : Fin d, (B i).IsTree) →
      rootedForestProduct V B r = independentDeletionTransform V B r

end

end MathlibPlus.Open.ResearchFormalization.R0523Claim22328
