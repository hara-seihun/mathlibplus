import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

namespace MathlibPlus.Open.NewResearch2.R0523RootedSID

noncomputable section

open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev UPolynomial := MvPolynomial ℕ ℤ
private abbrev ShiftedPolynomial := MvPolynomial (Option ℕ) ℤ

private def componentVertices {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (C : F.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v => F.connectedComponentMk v = C)

private def equalBlockRootedForest {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) (m d : ℕ) : Prop :=
  F.IsAcyclic ∧ R.card = d ∧
    ∀ C : F.ConnectedComponent,
      (componentVertices F C).card = m ∧
        (R ∩ componentVertices F C).card = 1

private def deletedVertices {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  F.induce {v : V | v ∉ S}

private def deletedUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : UPolynomial :=
  MvPolynomial.map (Nat.castRingHom ℤ)
    (MathlibPlus.Open.ResearchFormalizationBatch.graphUPolynomial
      (deletedVertices F S))

private def noSingletonUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : UPolynomial :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* UPolynomial)
    (fun n : ℕ => if n = 1 then 0 else (MvPolynomial.X n : UPolynomial))
    (deletedUPolynomial F S)

private def independentVertexSet {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ F.Adj u v

private def inducedStarMultiplicity {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (R J : Finset V) : ℕ :=
  (J.filter (fun v =>
    independentVertexSet F (J.erase v) ∧
      (J.erase v ∩ R).card = 0)).card

private def inducedStarLayer {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) (q : ℕ) : UPolynomial :=
  ∑ J ∈ ((Finset.univ : Finset V).powerset).filter
      (fun J => J.card = q + 1),
    (inducedStarMultiplicity F R J : ℤ) • deletedUPolynomial F J

private def inducedStarDeck {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) : Polynomial UPolynomial :=
  ∑ J ∈ ((Finset.univ : Finset V).powerset).filter (fun J => J.Nonempty),
    Polynomial.C ((inducedStarMultiplicity F R J : ℤ) • deletedUPolynomial F J) *
      (-Polynomial.X) ^ (J.card - 1)

private def inducedStarLayersEqual {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (R : Finset V)
    (G : SimpleGraph W) (S : Finset W) : Prop :=
  ∀ q : ℕ, inducedStarLayer F R q = inducedStarLayer G S q

private def noSingletonIndependentDeletionLayer
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V) (q : ℕ) : UPolynomial :=
  ∑ I ∈ ((Finset.univ : Finset V).powerset).filter (fun I =>
      I.card = q ∧ independentVertexSet F I ∧ (I ∩ R).card = 0),
    noSingletonUPolynomial F I

private def leastNoSingletonDiscrepancy
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (R : Finset V)
    (G : SimpleGraph W) (S : Finset W) : Prop :=
  ∃ q : ℕ,
    (∀ p : ℕ, p < q →
      noSingletonIndependentDeletionLayer F R p =
        noSingletonIndependentDeletionLayer G S p) ∧
    noSingletonIndependentDeletionLayer F R q ≠
      noSingletonIndependentDeletionLayer G S q

private def decisiveSIDCounterexample
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (R : Finset V)
    (G : SimpleGraph W) (S : Finset W) (m d : ℕ) : Prop :=
  equalBlockRootedForest F R m d ∧
    equalBlockRootedForest G S m d ∧
    inducedStarLayersEqual F R G S ∧
    leastNoSingletonDiscrepancy F R G S

/-- Claim 22337: equality of the induced-star decks is exactly equality in
all homogeneous q-layers, and the decisive SID counterexample criterion keeps
the equal-block rooted forests and the least differing no-singleton layer. -/
def claim22337 : Prop :=
  (∀ {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (R : Finset V)
    (G : SimpleGraph W) (S : Finset W) (m d : ℕ),
    equalBlockRootedForest F R m d →
    equalBlockRootedForest G S m d →
      (inducedStarDeck F R = inducedStarDeck G S ↔
        inducedStarLayersEqual F R G S)) ∧
  (∀ {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (R : Finset V)
    (G : SimpleGraph W) (S : Finset W) (m d : ℕ),
    decisiveSIDCounterexample F R G S m d ↔
      (equalBlockRootedForest F R m d ∧
        equalBlockRootedForest G S m d ∧
        inducedStarLayersEqual F R G S ∧
        leastNoSingletonDiscrepancy F R G S))

private def ordinaryYDegree (a : (Option ℕ) →₀ ℕ) : ℕ :=
  a.sum (fun i e => match i with | none => 0 | some _ => e)

private def ordinaryYDegreeOne (p : ShiftedPolynomial) : ShiftedPolynomial :=
  ∑ a ∈ p.support.filter (fun a => ordinaryYDegree a = 1),
    MvPolynomial.monomial a (MvPolynomial.coeff a p)

private def renameUToY (p : UPolynomial) : ShiftedPolynomial :=
  MvPolynomial.rename (fun n : ℕ => some n) p

private def shiftedRootFactor {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ShiftedPolynomial :=
  ∑ I ∈ ((Finset.univ : Finset V).powerset).filter (fun I =>
      independentVertexSet B I ∧ r ∉ I),
    (-MvPolynomial.X none) ^ I.card *
      renameUToY (deletedUPolynomial B I)

private def nonrootLeafCount {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ℕ :=
  (Finset.univ.filter (fun v => v ≠ r ∧ B.degree v = 1)).card

private def leafLayerForm {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V) : ShiftedPolynomial :=
  ∑ k ∈ Finset.range (nonrootLeafCount B r + 1),
    (Nat.choose (nonrootLeafCount B r) k : ℤ) •
      ((-MvPolynomial.X none) ^ k *
        MvPolynomial.X (some (Fintype.card V - k)))

private def noSingletonShifted (p : ShiftedPolynomial) : ShiftedPolynomial :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* ShiftedPolynomial)
    (fun i : Option ℕ =>
      if i = some 1 then 0 else (MvPolynomial.X i : ShiftedPolynomial)) p

private def ordinaryYHomogeneous (n : ℕ)
    (p : ShiftedPolynomial) : ShiftedPolynomial :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.filter (fun a : (Option ℕ) →₀ ℕ => ordinaryYDegree a = n) p.1)

private def dFactorNoSingletonLayer {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i))
    (r : ∀ i : Fin d, V i) : ShiftedPolynomial :=
  ordinaryYHomogeneous d
    (noSingletonShifted
      (∏ i : Fin d, shiftedRootFactor (B i) (r i)))

private def dFactorLeafLayer {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i))
    (r : ∀ i : Fin d, V i) : ShiftedPolynomial :=
  ∏ i : Fin d, noSingletonShifted (leafLayerForm (B i) (r i))

/-- Claim 22340: the ordinary y-degree-one shifted factor is the exact
nonroot-leaf binomial form, and the first no-singleton layer of d equal-order
factors is the product of those truncated forms. -/
def claim22340 : Prop :=
  (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (r : V),
    B.IsTree →
      ordinaryYDegreeOne (shiftedRootFactor B r) = leafLayerForm B r) ∧
  (∀ {d : ℕ}
    (V : Fin d → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : ∀ i : Fin d, SimpleGraph (V i))
    (r : ∀ i : Fin d, V i) (m : ℕ),
    0 < d →
    (∀ i : Fin d, (B i).IsTree ∧ Fintype.card (V i) = m) →
      dFactorNoSingletonLayer V B r = dFactorLeafLayer V B r)

end

end MathlibPlus.Open.NewResearch2.R0523RootedSID
