import Mathlib

namespace MathlibPlus.Open.CategoryTheory.PartitionRefinedProfiles.Claim23119

open scoped BigOperators

noncomputable section

private structure Pseudograph (V E : Type*) where
  source : E → V
  target : E → V

private structure PseudographCospan (I O V E : Type*) where
  graph : Pseudograph V E
  input : I → V
  output : O → V

private structure RefinedAtom (L : Type*) where
  size : ℕ
  edgeCount : ℕ
  labels : Finset L
  partition : Finset (Finset L)

private structure UnrefinedAtom (L : Type*) where
  size : ℕ
  labels : Finset L
  partition : Finset (Finset L)

private def pushoutGenerator {I O P V W E F : Type*}
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F) :
    Sum V W → Sum V W → Prop
  | Sum.inl v, Sum.inr w => ∃ p, G.output p = v ∧ H.input p = w
  | Sum.inr w, Sum.inl v => ∃ p, G.output p = v ∧ H.input p = w
  | _, _ => False

private def pushoutRelation {I O P V W E F : Type*}
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F) :
    Sum V W → Sum V W → Prop :=
  Relation.EqvGen (pushoutGenerator G H)

private abbrev PushoutVertex {I O P V W E F : Type*}
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F) :=
  Finset (Sum V W)

private noncomputable def pushoutMk {I O P V W E F : Type*}
    [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (v : Sum V W) : PushoutVertex G H :=
  letI := Classical.decEq (Sum V W)
  letI := Classical.propDecidable
  Finset.univ.filter (pushoutRelation G H v)

private def composeCospan {I O P V W E F : Type*}
    [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F) :
    PseudographCospan I P (PushoutVertex G H) (Sum E F) :=
  { graph :=
      { source := Sum.elim
          (fun e => pushoutMk G H (Sum.inl (G.graph.source e)))
          (fun f => pushoutMk G H (Sum.inr (H.graph.source f)))
        target := Sum.elim
          (fun e => pushoutMk G H (Sum.inl (G.graph.target e)))
          (fun f => pushoutMk G H (Sum.inr (H.graph.target f))) }
    input := fun i => pushoutMk G H (Sum.inl (G.input i))
    output := fun p => pushoutMk G H (Sum.inr (H.output p)) }

private def tensorCospan {I O I' O' V W E F : Type*}
    (G : PseudographCospan I O V E) (H : PseudographCospan I' O' W F) :
    PseudographCospan (Sum I I') (Sum O O') (Sum V W) (Sum E F) :=
  { graph :=
      { source := Sum.elim (fun e => Sum.inl (G.graph.source e))
          (fun f => Sum.inr (H.graph.source f))
        target := Sum.elim (fun e => Sum.inl (G.graph.target e))
          (fun f => Sum.inr (H.graph.target f)) }
    input := Sum.elim (fun i => Sum.inl (G.input i))
      (fun i' => Sum.inr (H.input i'))
    output := Sum.elim (fun o => Sum.inl (G.output o))
      (fun o' => Sum.inr (H.output o')) }

private noncomputable def selectedComposite {E F : Type*}
    (A : Finset E) (B : Finset F) : Finset (Sum E F) :=
  letI := Classical.decEq (Sum E F)
  A.image Sum.inl ∪ B.image Sum.inr

private noncomputable def selectedAdjacent {V E : Type*}
    (G : Pseudograph V E) (A : Finset E) (u v : V) : Prop :=
  ∃ e ∈ A,
    (G.source e = u ∧ G.target e = v) ∨
      (G.source e = v ∧ G.target e = u)

private def selectedReach {V E : Type*}
    (G : Pseudograph V E) (A : Finset E) : V → V → Prop :=
  Relation.ReflTransGen (selectedAdjacent G A)

private noncomputable def selectedComponent {V E : Type*}
    [Fintype V] (G : Pseudograph V E) (A : Finset E) (v : V) : Finset V :=
  letI := Classical.decEq V
  letI := Classical.decEq E
  letI := Classical.propDecidable
  Finset.univ.filter (selectedReach G A v)

private noncomputable def selectedComponents {V E : Type*}
    [Fintype V] (G : Pseudograph V E) (A : Finset E) : Finset (Finset V) :=
  letI := Classical.decEq V
  letI := Classical.decEq E
  letI := Classical.propDecidable
  Finset.univ.image (selectedComponent G A)

private noncomputable def componentPartition {L V : Type*}
    [Fintype L] [Fintype V] (boundary : L → V) (S : Finset L) : Finset (Finset L) :=
  letI := Classical.decEq L
  letI := Classical.decEq V
  letI := Classical.propDecidable
  (Finset.univ.image (fun v => S.filter (fun l => boundary l = v))).filter
    Finset.Nonempty

private noncomputable def componentAtom {L V E : Type*}
    [Fintype L] [Fintype V] (G : Pseudograph V E) (A : Finset E)
    (boundary : L → V) (C : Finset V) : RefinedAtom L :=
  letI := Classical.decEq L
  letI := Classical.decEq V
  letI := Classical.decEq E
  letI := Classical.propDecidable
  let S := Finset.univ.filter (fun l => boundary l ∈ C)
  { size := C.card
    edgeCount := (A.filter (fun e => G.source e ∈ C ∨ G.target e ∈ C)).card
    labels := S
    partition := componentPartition boundary S }

private noncomputable def refinedProfile {I O V E : Type*}
    [Fintype I] [Fintype O] [Fintype V]
    (G : PseudographCospan I O V E) (A : Finset E) :
    Multiset (RefinedAtom (Sum I O)) :=
  letI := Classical.decEq I
  letI := Classical.decEq O
  letI := Classical.decEq V
  letI := Classical.decEq E
  (selectedComponents G.graph A).val.map
    (fun C => componentAtom G.graph A (Sum.elim G.input G.output) C)

private def forgetEdge (a : RefinedAtom L) : UnrefinedAtom L :=
  { size := a.size, labels := a.labels, partition := a.partition }

private noncomputable def unrefinedProfile {I O V E : Type*}
    [Fintype I] [Fintype O] [Fintype V]
    (G : PseudographCospan I O V E) (A : Finset E) :
    Multiset (UnrefinedAtom (Sum I O)) :=
  (refinedProfile G A).map forgetEdge

private noncomputable def profileComposite {I O P V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype P]
    [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F) :
    Multiset (RefinedAtom (Sum I P)) :=
  refinedProfile (composeCospan G H) (selectedComposite A B)

private noncomputable def profileTensor {I O I' O' V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan I' O' W F)
    (A : Finset E) (B : Finset F) :
    Multiset (RefinedAtom (Sum (Sum I I') (Sum O O'))) :=
  refinedProfile (tensorCospan G H) (selectedComposite A B)

private noncomputable def mapAtom {L L' : Type*}
    (f : L → L') (a : RefinedAtom L) : RefinedAtom L' :=
  letI := Classical.decEq L'
  { size := a.size
    edgeCount := a.edgeCount
    labels := a.labels.image f
    partition := a.partition.image (fun B => B.image f) }

private noncomputable def mapProfile {L L' : Type*} (f : L → L')
    (p : Multiset (RefinedAtom L)) : Multiset (RefinedAtom L') :=
  p.map (mapAtom f)

private def leftTensorLabel {I O I' O' : Type*} :
    Sum I O → Sum (Sum I I') (Sum O O')
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr o => Sum.inr (Sum.inl o)

private def rightTensorLabel {I O I' O' : Type*} :
    Sum I' O' → Sum (Sum I I') (Sum O O')
  | Sum.inl i => Sum.inl (Sum.inr i)
  | Sum.inr o => Sum.inr (Sum.inr o)

private noncomputable def relabelCospan {I O I' O' V E : Type*}
    (i : I ≃ I') (o : O ≃ O') (G : PseudographCospan I O V E) :
    PseudographCospan I' O' V E :=
  { graph := G.graph
    input := G.input ∘ i.symm
    output := G.output ∘ o.symm }

private def sumBoundaryMap {I O I' O' : Type*}
    (i : I ≃ I') (o : O ≃ O') : Sum I O → Sum I' O' :=
  Sum.map i o

private def identityCospan (I : Type*) :
    PseudographCospan I I I Empty :=
  { graph := { source := Empty.elim, target := Empty.elim }
    input := id
    output := id }

private noncomputable def identityAtomShape {I : Type*}
    (i : I) (a : RefinedAtom (Sum I I)) : Prop :=
  letI := Classical.decEq (Sum I I)
  let labels : Finset (Sum I I) :=
    {(Sum.inl i : Sum I I), (Sum.inr i : Sum I I)}
  let block : Finset (Sum I I) :=
    {(Sum.inl i : Sum I I), (Sum.inr i : Sum I I)}
  a.size = 1 ∧ a.edgeCount = 0 ∧ a.labels = labels ∧
    a.partition = ({block} : Finset (Finset (Sum I I)))

private noncomputable def identityProfileShape {I : Type*}
    [Fintype I] (p : Multiset (RefinedAtom (Sum I I))) : Prop :=
  p.card = Fintype.card I ∧
    (∀ i : I, ∃ a ∈ p, identityAtomShape i a) ∧
      (∀ a, a ∈ p → ∃ i : I, identityAtomShape i a)

private noncomputable def edgeTotal {L : Type*}
    (p : Multiset (RefinedAtom L)) : ℕ :=
  (p.map RefinedAtom.edgeCount).sum

private def refinedProfileAssociative : Prop :=
  ∀ {I O P Q V W X E F K : Type}
    [Fintype I] [Fintype O] [Fintype P] [Fintype Q]
    [Fintype V] [Fintype W] [Fintype X]
    [Fintype E] [Fintype F] [Fintype K]
    (G : PseudographCospan I O V E)
    (H : PseudographCospan O P W F)
    (J : PseudographCospan P Q X K)
    (A : Finset E) (B : Finset F) (C : Finset K),
    profileComposite (composeCospan G H) J (selectedComposite A B) C =
      profileComposite G (composeCospan H J) A (selectedComposite B C)

private def refinedProfileUnital : Prop :=
  ∀ {I O V E : Type} [Fintype I] [Fintype O] [Fintype V] [Fintype E]
    (G : PseudographCospan I O V E) (A : Finset E),
    profileComposite (identityCospan I) G (∅ : Finset Empty) A =
        refinedProfile G A ∧
      profileComposite G (identityCospan O) A (∅ : Finset Empty) =
        refinedProfile G A

private def refinedProfileComponentMultiplicative : Prop :=
  ∀ {I O I' O' V W E F : Type}
    [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    [Fintype V] [Fintype W] [Fintype E] [Fintype F]
    (G : PseudographCospan I O V E)
    (H : PseudographCospan I' O' W F)
    (A : Finset E) (B : Finset F),
    profileTensor G H A B =
      mapProfile (leftTensorLabel (I := I) (O := O) (I' := I') (O' := O'))
          (refinedProfile G A) +
        mapProfile (rightTensorLabel (I := I) (O := O) (I' := I') (O' := O'))
          (refinedProfile H B)

private def refinedProfileRelabelingNatural : Prop :=
  ∀ {I O I' O' V E : Type}
    [Fintype I] [Fintype O] [Fintype I'] [Fintype O'] [Fintype V] [Fintype E]
    (i : I ≃ I') (o : O ≃ O')
    (G : PseudographCospan I O V E) (A : Finset E),
    refinedProfile (relabelCospan i o G) A =
      mapProfile (sumBoundaryMap i o) (refinedProfile G A)

private def compositeBoundaryMap {I O P V W E F : Type*}
    [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F) :
    Sum I P → PushoutVertex G H :=
  Sum.elim
    (fun i => pushoutMk G H (Sum.inl (G.input i)))
    (fun p => pushoutMk G H (Sum.inr (H.output p)))

private noncomputable def finalBoundaryLabels {I O P V W E F : Type*}
    [Fintype I] [Fintype P] [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (C : Finset (PushoutVertex G H)) : Finset (Sum I P) :=
  letI := Classical.decEq I
  letI := Classical.decEq O
  letI := Classical.decEq P
  letI := Classical.decEq V
  letI := Classical.decEq W
  letI := Classical.decEq E
  letI := Classical.decEq F
  letI := Classical.decEq (PushoutVertex G H)
  Finset.univ.filter (fun x => compositeBoundaryMap G H x ∈ C)

private noncomputable def leftSourcesInCluster {I O P V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype P] [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F)
    (C : Finset (PushoutVertex G H)) : Finset (Finset V) :=
  letI := Classical.decEq I
  letI := Classical.decEq O
  letI := Classical.decEq P
  letI := Classical.decEq V
  letI := Classical.decEq W
  letI := Classical.decEq E
  letI := Classical.decEq F
  letI := Classical.decEq (PushoutVertex G H)
  (selectedComponents G.graph A).filter (fun S =>
    ∀ v, v ∈ S → pushoutMk G H (Sum.inl v) ∈ C)

private noncomputable def rightSourcesInCluster {I O P V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype P] [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F)
    (C : Finset (PushoutVertex G H)) : Finset (Finset W) :=
  letI := Classical.decEq I
  letI := Classical.decEq O
  letI := Classical.decEq P
  letI := Classical.decEq V
  letI := Classical.decEq W
  letI := Classical.decEq E
  letI := Classical.decEq F
  letI := Classical.decEq (PushoutVertex G H)
  (selectedComponents H.graph B).filter (fun S =>
    ∀ w, w ∈ S → pushoutMk G H (Sum.inr w) ∈ C)

private noncomputable def sourceClusterInternalSum {I O P V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype P] [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F)
    (C : Finset (PushoutVertex G H)) : ℕ :=
  let left := leftSourcesInCluster G H A B C
  let right := rightSourcesInCluster G H A B C
  left.sum (fun S =>
      let a := componentAtom G.graph A (Sum.elim G.input G.output) S
      a.size - a.partition.card) +
    right.sum (fun S =>
      let a := componentAtom H.graph B (Sum.elim H.input H.output) S
      a.size - a.partition.card)

private noncomputable def sourceClusterEdgeSum {I O P V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype P] [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F)
    (C : Finset (PushoutVertex G H)) : ℕ :=
  (leftSourcesInCluster G H A B C).sum (fun S =>
      (componentAtom G.graph A (Sum.elim G.input G.output) S).edgeCount) +
    (rightSourcesInCluster G H A B C).sum (fun S =>
      (componentAtom H.graph B (Sum.elim H.input H.output) S).edgeCount)

private noncomputable def clusterJoinAtom {I O P V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype P] [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F)
    (C : Finset (PushoutVertex G H)) : RefinedAtom (Sum I P) :=
  letI := Classical.decEq I
  letI := Classical.decEq O
  letI := Classical.decEq P
  letI := Classical.decEq V
  letI := Classical.decEq W
  letI := Classical.decEq E
  letI := Classical.decEq F
  letI := Classical.decEq (PushoutVertex G H)
  let S := finalBoundaryLabels G H C
  { size := sourceClusterInternalSum G H A B C +
      (componentPartition (compositeBoundaryMap G H) S).card
    edgeCount := sourceClusterEdgeSum G H A B C
    labels := S
    partition := componentPartition (compositeBoundaryMap G H) S }

private noncomputable def partitionJoinProfile {I O P V W E F : Type*}
    [Fintype I] [Fintype O] [Fintype P] [Fintype V] [Fintype W]
    (G : PseudographCospan I O V E) (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F) : Multiset (RefinedAtom (Sum I P)) :=
  letI := Classical.decEq I
  letI := Classical.decEq O
  letI := Classical.decEq P
  letI := Classical.decEq V
  letI := Classical.decEq W
  letI := Classical.decEq E
  letI := Classical.decEq F
  letI := Classical.decEq (PushoutVertex G H)
  (selectedComponents (composeCospan G H).graph (selectedComposite A B)).val.map
    (clusterJoinAtom G H A B)

private def partitionJoinClusterLaws : Prop :=
  ∀ {I O P V W E F : Type}
    [Fintype I] [Fintype O] [Fintype P]
    [Fintype V] [Fintype W] [Fintype E] [Fintype F]
    (G : PseudographCospan I O V E)
    (H : PseudographCospan O P W F)
    (A : Finset E) (B : Finset F),
    letI := Classical.decEq (PushoutVertex G H)
    refinedProfile (composeCospan G H) (selectedComposite A B) =
        partitionJoinProfile G H A B ∧
      (∀ C ∈ selectedComponents (composeCospan G H).graph
          (selectedComposite A B),
        (componentAtom (composeCospan G H).graph (selectedComposite A B)
            (compositeBoundaryMap G H) C).edgeCount =
            sourceClusterEdgeSum G H A B C ∧
          (componentAtom (composeCospan G H).graph (selectedComposite A B)
            (compositeBoundaryMap G H) C).size =
            sourceClusterInternalSum G H A B C +
              (componentPartition (compositeBoundaryMap G H)
                (finalBoundaryLabels G H C)).card)

private def refinedProfilePushoutCompatible : Prop :=
  partitionJoinClusterLaws

private def emptyPortCospan {V E : Type*}
    (G : Pseudograph V E) : PseudographCospan (Fin 0) (Fin 0) V E :=
  { graph := G
    input := Fin.elim0
    output := Fin.elim0 }

private noncomputable def xVar (n : ℕ) : MvPolynomial ℕ ℕ :=
  MvPolynomial.X n

private noncomputable def txVar (n : ℕ) : MvPolynomial (Sum Unit ℕ) ℕ :=
  MvPolynomial.X (Sum.inr n)

private noncomputable def tVar : MvPolynomial (Sum Unit ℕ) ℕ :=
  MvPolynomial.X (Sum.inl ())

private noncomputable def intTVar : MvPolynomial (Sum Unit ℕ) ℤ :=
  MvPolynomial.X (Sum.inl ())

private noncomputable def closedUnrefinedInvariant {V E : Type*}
    [Fintype V] [Fintype E] (G : Pseudograph V E) : MvPolynomial ℕ ℕ :=
  letI := Classical.decEq V
  letI := Classical.decEq E
  letI := Classical.propDecidable
  ∑ A : Finset E,
    ∏ C ∈ selectedComponents G A, xVar C.card

private noncomputable def closedRefinedInvariant {V E : Type*}
    [Fintype V] [Fintype E] (G : Pseudograph V E) :
    MvPolynomial (Sum Unit ℕ) ℕ :=
  letI := Classical.decEq V
  letI := Classical.decEq E
  letI := Classical.propDecidable
  ∑ A : Finset E,
    tVar ^ A.card * ∏ C ∈ selectedComponents G A, txVar C.card

private def edgeCountInvariantFactorsThroughU : Prop :=
  ∃ φ : MvPolynomial ℕ ℕ →+* MvPolynomial (Sum Unit ℕ) ℕ,
    ∀ {V E : Type} [Fintype V] [Fintype E]
      (G : Pseudograph V E),
      closedRefinedInvariant G = φ (closedUnrefinedInvariant G)

private def triangleGraph3 : Pseudograph (Fin 3) (Fin 3) :=
  { source := fun e => e
    target := fun e => if e = 0 then 1 else if e = 1 then 2 else 0 }

private def triangleProfileWitness : Prop :=
  let pathSelection : Finset (Fin 3) := {0, 1}
  let triangleSelection : Finset (Fin 3) := Finset.univ
  unrefinedProfile (emptyPortCospan triangleGraph3) pathSelection =
      unrefinedProfile (emptyPortCospan triangleGraph3) triangleSelection ∧
    edgeTotal (refinedProfile (emptyPortCospan triangleGraph3) pathSelection) ≠
      edgeTotal (refinedProfile (emptyPortCospan triangleGraph3) triangleSelection)

private def triangleClosedInvariantReceipt : Prop :=
  closedUnrefinedInvariant triangleGraph3 =
      xVar 1 ^ 3 + 3 * xVar 1 * xVar 2 + 4 * xVar 3 ∧
    closedRefinedInvariant triangleGraph3 =
      txVar 1 ^ 3 + 3 * tVar * txVar 1 * txVar 2 +
        (3 * tVar ^ 2 + tVar ^ 3) * txVar 3 ∧
    3 * tVar ^ 2 + tVar ^ 3 ≠ 4 * tVar ^ 2 ∧
    (3 * intTVar ^ 2 + intTVar ^ 3) - 4 * intTVar ^ 2 =
      intTVar ^ 2 * (intTVar - 1)

private def edgeCountDoesNotFactorThroughU : Prop :=
  ¬ edgeCountInvariantFactorsThroughU

private structure BoundaryComponent (L : Type*) where
  vertexCount : ℕ
  edgeCount : ℕ
  source : Fin edgeCount → Fin vertexCount
  target : Fin edgeCount → Fin vertexCount
  selected : Finset (Fin edgeCount)
  boundary : L → Fin vertexCount

private def componentStep {L : Type*} (C : BoundaryComponent L)
    (u v : Fin C.vertexCount) : Prop :=
  ∃ e ∈ C.selected,
    (C.source e = u ∧ C.target e = v) ∨
      (C.source e = v ∧ C.target e = u)

private def connectedBoundaryComponent {L : Type*}
    (C : BoundaryComponent L) : Prop :=
  ∀ u v, Relation.ReflTransGen (componentStep C) u v

private def boundaryPreservingIso {L : Type*}
    (C D : BoundaryComponent L) : Prop :=
  ∃ eV : Fin C.vertexCount ≃ Fin D.vertexCount,
    ∃ eE : Fin C.edgeCount ≃ Fin D.edgeCount,
      (∀ e, eV (C.source e) = D.source (eE e) ∧
        eV (C.target e) = D.target (eE e)) ∧
      (∀ e, e ∈ C.selected ↔ eE e ∈ D.selected) ∧
      (∀ l, eV (C.boundary l) = D.boundary l)

private def componentEdgeAtom {L : Type*} [Fintype L]
    (C : BoundaryComponent L) : RefinedAtom L :=
  letI := Classical.decEq L
  { size := C.vertexCount
    edgeCount := C.selected.card
    labels := Finset.univ
    partition := componentPartition C.boundary Finset.univ }

private def componentUnrefinedAtom {L : Type*} [Fintype L]
    (C : BoundaryComponent L) : UnrefinedAtom L :=
  forgetEdge (componentEdgeAtom C)

private def edgeCountComponentEvaluation {L : Type*}
    (C : BoundaryComponent L) : ℕ :=
  C.selected.card

private def edgeCountEvaluationFactors : Prop :=
  ∀ {L : Type} [Fintype L],
    ∃ factor : RefinedAtom L → ℕ,
      ∀ C, connectedBoundaryComponent C →
        factor (componentEdgeAtom C) = C.selected.card

private def refinedAtomUniversalForComponentLocalInvariants : Prop :=
  ∀ {L : Type} [Fintype L] (D : Type)
    (evaluation : BoundaryComponent L → D),
    ((∃ factor : RefinedAtom L → D,
        ∀ C, connectedBoundaryComponent C →
          factor (componentEdgeAtom C) = evaluation C) ↔
      ∀ C C', connectedBoundaryComponent C → connectedBoundaryComponent C' →
        componentEdgeAtom C = componentEdgeAtom C' → evaluation C = evaluation C')

private def fullComponentClass {L : Type}
    (C : BoundaryComponent L) : Set (BoundaryComponent L) :=
  {D | boundaryPreservingIso C D}

private def fullComponentTypeUniversalForComponentLocalInvariants : Prop :=
  ∀ {L : Type} (D : Type)
    (evaluation : BoundaryComponent L → D),
    (∀ C C', connectedBoundaryComponent C → connectedBoundaryComponent C' →
      boundaryPreservingIso C C' → evaluation C = evaluation C') →
      ∃ factor : Set (BoundaryComponent L) → D,
        ∀ C, connectedBoundaryComponent C →
          factor (fullComponentClass C) = evaluation C

private def everyCoarserQuotientCriterion : Prop :=
  ∀ {L : Type} (Q D : Type)
    (q : BoundaryComponent L → Q)
    (evaluation : BoundaryComponent L → D),
    Function.Surjective q →
      ((∃ factor : Q → D, ∀ C, factor (q C) = evaluation C) ↔
        ∀ C C', q C = q C' → evaluation C = evaluation C')

private def pathComponent : BoundaryComponent (Fin 0) :=
  { vertexCount := 3
    edgeCount := 2
    source := fun e => if e = 0 then 0 else 1
    target := fun e => if e = 0 then 1 else 2
    selected := Finset.univ
    boundary := Fin.elim0 }

private def triangleComponent : BoundaryComponent (Fin 0) :=
  { vertexCount := 3
    edgeCount := 3
    source := fun e => e
    target := fun e => if e = 0 then 1 else if e = 1 then 2 else 0
    selected := Finset.univ
    boundary := Fin.elim0 }

private def edgeCountRefinementTriangleWitness : Prop :=
  connectedBoundaryComponent pathComponent ∧
    connectedBoundaryComponent triangleComponent ∧
      componentUnrefinedAtom pathComponent =
          componentUnrefinedAtom triangleComponent ∧
        componentEdgeAtom pathComponent ≠ componentEdgeAtom triangleComponent

def exactFactorizationRepairs_claim23119 : Prop :=
  edgeCountEvaluationFactors ∧
    refinedAtomUniversalForComponentLocalInvariants ∧
      edgeCountRefinementTriangleWitness ∧
        fullComponentTypeUniversalForComponentLocalInvariants ∧
          everyCoarserQuotientCriterion

end

end MathlibPlus.Open.CategoryTheory.PartitionRefinedProfiles.Claim23119
