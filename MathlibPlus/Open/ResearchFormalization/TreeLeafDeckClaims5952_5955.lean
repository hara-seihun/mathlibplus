import MathlibPlus.Open.TreeSpectral

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.TreeLeafDeckClaims5952_5955

noncomputable section

open MathlibPlus.Open.TreeSpectral
attribute [local instance] Classical.propDecidable Classical.decEq

private def leafDeckExpansion (n : ℕ) (q : TreeClass n) : TreeSpace (n - 1) :=
  let T := Quotient.out q
  ∑ ℓ : Fin n, ∑ u : TreeClass (n - 1),
    Finsupp.single u
      (if IsLeaf T.1 ℓ ∧
          GraphIso (T.1.induce {x : Fin n | x ≠ ℓ}) (Quotient.out u).1 then
        (1 : ℚ) else 0)

private def graftDeckExpansion (n : ℕ) (q : TreeClass n) : TreeSpace (n + 1) :=
  let T := Quotient.out q
  ∑ v : Fin n, ∑ u : TreeClass (n + 1),
    Finsupp.single u
      (if GraphIso (graftGraph T.1 v) (Quotient.out u).1 then
        (1 : ℚ) else 0)

private def loweringMap (n : ℕ) :
    TreeSpace (n + 1) →ₗ[ℚ] TreeSpace n :=
  (transportTreeSpace
    (Nat.add_right_cancel
      (Nat.sub_add_cancel (Nat.succ_le_succ (Nat.zero_le n))))).comp
    (leafDeletion (n + 1))

private def previousRaisingMap (n : ℕ) (h : 1 ≤ n) :
    TreeSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  (transportTreeSpace (Nat.sub_add_cancel h)).comp (graft (n - 1))

private def eMap (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace (n + 1) :=
  graft n

private def fMap (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace (n - 1) :=
  (-2 : ℚ) • leafDeletion n

private def fNextMap (n : ℕ) :
    TreeSpace (n + 1) →ₗ[ℚ] TreeSpace n :=
  (-2 : ℚ) • loweringMap n

private def hMap (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace n :=
  (2 * (n : ℚ)) • (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n)

/-- Claim 5952: the fixed-vertex tree quotient and its free rational span. -/
def unrootedTreeLevelSpace_claim5952 : Prop :=
  ∀ n : ℕ,
    (∀ G H : TreeGraph n,
      (Quotient.mk (TreeGraphSetoid n) G : TreeClass n) =
          Quotient.mk (TreeGraphSetoid n) H ↔
        Nonempty (G.1 ≃g H.1)) ∧
    Nonempty (Module.Basis (TreeClass n) ℚ (TreeSpace n))

/-- Claim 5953: the canonical leaf, graft, and grading actions on each basis level. -/
def leafDeletionGraftingAndGrading_claim5953 : Prop :=
  ∀ (n : ℕ) (q : TreeClass n),
    leafDeletion n (Finsupp.single q 1) = leafDeckExpansion n q ∧
    graft n (Finsupp.single q 1) = graftDeckExpansion n q ∧
    (∀ x : TreeSpace n,
      ((n : ℚ) • (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n)) x =
        (n : ℚ) • x)

/-- Claim 5954: the stable graft/prune commutator on every degree n at least two. -/
def stableRangeGraftPruneCommutator_claim5954 : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ h : 1 ≤ n,
      (loweringMap n).comp (graft n) -
          (previousRaisingMap n h).comp (leafDeletion n) =
        (n : ℚ) • (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n)

/-- Claim 5955: e=G, f=-2L, h=2N satisfy the stable sl2 commutators. -/
def stableSL2Relations_claim5955 : Prop :=
  (∀ (n : ℕ), 2 ≤ n →
    ∀ h : 1 ≤ n,
      (previousRaisingMap n h).comp (fMap n) -
          (fNextMap n).comp (eMap n) = hMap n) ∧
  (∀ (n : ℕ), 2 ≤ n →
    (hMap (n + 1)).comp (eMap n) -
        (eMap n).comp (hMap n) = (2 : ℚ) • eMap n) ∧
  (∀ (n : ℕ), 2 ≤ n → 2 ≤ n - 1 →
    (hMap (n - 1)).comp (fMap n) -
        (fMap n).comp (hMap n) = (-2 : ℚ) • fMap n)

end
end MathlibPlus.Open.ResearchFormalization.TreeLeafDeckClaims5952_5955
