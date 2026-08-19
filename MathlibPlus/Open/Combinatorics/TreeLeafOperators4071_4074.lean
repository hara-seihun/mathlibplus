import MathlibPlus.Open.TreeSpectral

open scoped BigOperators

noncomputable section
open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.Combinatorics.TreeLeafOperators

abbrev TreeClass (n : ℕ) := MathlibPlus.Open.TreeSpectral.TreeClass n
abbrev TreeSpace (n : ℕ) := MathlibPlus.Open.TreeSpectral.TreeSpace n

open MathlibPlus.Open.TreeSpectral

noncomputable def leafPruningOperator (n : ℕ) :
    TreeSpace n →ₗ[ℚ] TreeSpace (n - 1) :=
  leafDeletion n

noncomputable def leafGraftingOperator (n : ℕ) :
    TreeSpace n →ₗ[ℚ] TreeSpace (n + 1) :=
  graft n

noncomputable def treePairing {n : ℕ} (x y : TreeSpace n) : ℚ :=
  ∑ T : TreeClass n, x T * y T

/-- The leaf-deck operator on the free rational space of unlabelled trees. -/
def claim4071_leafPruningOperator : Prop :=
  ∀ (n : ℕ) (T : TreeClass n),
    leafPruningOperator n (Finsupp.single T (1 : ℚ)) =
      ∑ ℓ : Fin n, ∑ U : TreeClass (n - 1),
        Finsupp.single U
          (if IsLeaf (Quotient.out T).1 ℓ ∧
              GraphIso
                ((Quotient.out T).1.induce {x : Fin n | x ≠ ℓ})
                (Quotient.out U).1 then
            (1 : ℚ) else 0)

/-- The transpose of leaf pruning is vertexwise pendant-leaf grafting. -/
def claim4072_leafGraftingTranspose : Prop :=
  (∀ (n : ℕ) (x : TreeSpace (n + 1)) (y : TreeSpace n),
    treePairing (leafPruningOperator (n + 1) x) y =
      treePairing x (leafGraftingOperator n y)) ∧
  (∀ (n : ℕ) (C : TreeClass n),
    leafGraftingOperator n (Finsupp.single C (1 : ℚ)) =
      ∑ v : Fin n, ∑ T : TreeClass (n + 1),
        Finsupp.single T
          (if GraphIso
                (graftGraph (Quotient.out C).1 v)
                (Quotient.out T).1 then
            (1 : ℚ) else 0))

def treeLeafSet {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Fin n) :=
  {v | IsLeaf G v}

/-- Grafting at a nonleaf adds the new leaf and preserves all old leaves. -/
def claim4073_leavesAfterNonleafGrafting : Prop :=
  ∀ (n : ℕ) (C : TreeClass n) (v : Fin n),
    ¬ IsLeaf (Quotient.out C).1 v →
      treeLeafSet (graftGraph (Quotient.out C).1 v) =
          ({Fin.last n} : Set (Fin (n + 1))) ∪
            (Fin.castSucc '' treeLeafSet (Quotient.out C).1) ∧
        Disjoint ({Fin.last n} : Set (Fin (n + 1)))
          (Fin.castSucc '' treeLeafSet (Quotient.out C).1)

def deletedVertexGraph {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (ell' : Fin (n + 1)) : SimpleGraph (Fin n) :=
  SimpleGraph.comap (Fin.succAbove ell') G

/-- Replacing an adjacent leaf by a fresh pendant at its former neighbour. -/
def claim4074_adjacentLeafExchange : Prop :=
  ∀ (n : ℕ) (C : TreeClass (n + 1))
    (ell' v : Fin (n + 1)) (u : Fin n),
    IsLeaf (Quotient.out C).1 ell' ∧
      (Quotient.out C).1.Adj ell' v ∧
      Fin.succAbove ell' u = v →
      GraphIso
        (graftGraph (deletedVertexGraph (Quotient.out C).1 ell') u)
        (Quotient.out C).1

end MathlibPlus.Open.Combinatorics.TreeLeafOperators

end
