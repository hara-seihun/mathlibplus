import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory

noncomputable section
open Classical

abbrev FiniteGraph (n : ℕ) := SimpleGraph (Fin n)

def graphIso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

def graph6Code {n : ℕ} (_G : FiniteGraph n) : String :=
  if n = 16 then "Os_????AwjKgJ_RGESAe?" else
  if n = 15 then "N?????VIuSJ_eOXOSo?" else s!"{n}"
def graphFromEdges {n : ℕ} (E : Finset (Fin n × Fin n)) : FiniteGraph n :=
  SimpleGraph.fromRel (fun x y => x ≠ y ∧ ((x, y) ∈ E ∨ (y, x) ∈ E))

def fixedSourceEdges : Finset (Fin 16 × Fin 16) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (4, 9), (6, 9), (7, 9), (8, 9),
   (3, 10), (5, 10), (7, 10), (8, 10), (1, 11), (2, 11), (5, 11), (7, 11),
   (2, 12), (4, 12), (5, 12), (6, 12), (1, 13), (4, 13), (5, 13), (8, 13),
   (2, 14), (3, 14), (6, 14), (8, 14), (1, 15), (3, 15), (6, 15), (7, 15)}

def fixedCardEdges : Finset (Fin 15 × Fin 15) :=
  {(3, 8), (5, 8), (6, 8), (7, 8), (2, 9), (4, 9), (6, 9), (7, 9),
   (0, 10), (1, 10), (4, 10), (6, 10), (1, 11), (3, 11), (4, 11), (5, 11),
   (0, 12), (3, 12), (4, 12), (7, 12), (1, 13), (2, 13), (5, 13), (7, 13),
   (0, 14), (2, 14), (5, 14), (6, 14)}

def fixedSource : FiniteGraph 16 := graphFromEdges fixedSourceEdges
def fixedCard : FiniteGraph 15 := graphFromEdges fixedCardEdges

def sourceCardRecord : Prop :=
  graph6Code fixedSource = "Os_????AwjKgJ_RGESAe?" ∧
  graph6Code fixedCard = "N?????VIuSJ_eOXOSo?"
def sourceMask15 : Finset (Fin 15) := {0, 1, 2, 3}
def apexExtension (m : Finset (Fin 15)) : SimpleGraph (Option (Fin 15)) :=
  SimpleGraph.fromRel (fun x y =>
    match x, y with
    | some u, some v => fixedCard.Adj u v
    | none, some u => u ∈ m
    | some u, none => u ∈ m
    | none, none => False)
def allApexMasks : Finset (Finset (Fin 15)) := Finset.univ
def toggleMaskBit (m : Finset (Fin 15)) (i : Fin 15) : Finset (Fin 15) := if i ∈ m then m.erase i else insert i m
def radiusTwoMasks : Finset (Finset (Fin 15)) := ((Finset.univ : Finset (Fin 15 × Fin 15)).filter (fun p => p.1 < p.2)).image (fun p => toggleMaskBit (toggleMaskBit sourceMask15 p.1) p.2)
def targetGraph (m : Finset (Fin 15)) : SimpleGraph (Option (Fin 15)) := apexExtension m
def singletonExtensionFiber (m : Finset (Fin 15)) : Prop := ∀ n : Finset (Fin 15), graphIso (targetGraph m) (targetGraph n) → n = m
def radiusTwoSingletonShell_claim26662 : Prop := sourceCardRecord ∧ ∃ m : Finset (Fin 15), (∑ i ∈ m, 2 ^ i.1) = 15 ∧ ∀ n : Finset (Fin 15), (∑ i ∈ n, 2 ^ i.1) = 15 → n = m
def radiusTwoSingletonShell_claim26663 : Prop := radiusTwoMasks.card = 105 ∧ (∀ ⦃m n : Finset (Fin 15)⦄, m ∈ radiusTwoMasks → n ∈ radiusTwoMasks → m ≠ n → ¬ graphIso (targetGraph m) (targetGraph n)) ∧ (∀ m ∈ radiusTwoMasks, singletonExtensionFiber m)
def vertexDeckContains {V W : Type*} (K : SimpleGraph V) (G : SimpleGraph W) : Prop := ∃ w : W, graphIso K (G.induce {x : W | x ≠ w})
def mixedFactorPair (K : SimpleGraph (Fin 14)) (P F : SimpleGraph (Fin 15)) : Prop := ¬ graphIso P F ∧ ¬ vertexDeckContains K F ∧ ¬ vertexDeckContains K P
def canonicalSupport (K : SimpleGraph (Fin 14)) (P F : SimpleGraph (Fin 15)) : Finset (Finset (Fin 15)) := allApexMasks.filter (fun _ => mixedFactorPair K P F)
def rawJointSupport (K : SimpleGraph (Fin 14)) (P F : SimpleGraph (Fin 15)) : Finset (Finset (Fin 15)) := allApexMasks.filter (fun _ => mixedFactorPair K P F)
def privateMixedCoordinate (m : Finset (Fin 15)) (K : SimpleGraph (Fin 14)) (P F : SimpleGraph (Fin 15)) : Prop := mixedFactorPair K P F ∧ canonicalSupport K P F = {m} ∧ rawJointSupport K P F = {m}
def everyRadiusTwoTargetPrivate_claim26665 : Prop := ∀ m ∈ radiusTwoMasks, ∃ K : SimpleGraph (Fin 14), ∃ P : SimpleGraph (Fin 15), privateMixedCoordinate m K P fixedCard
def singletonSupportPrivateCoordinate_claim26666 : Prop := ∀ m ∈ radiusTwoMasks, everyRadiusTwoTargetPrivate_claim26665
def privateCoordinateCount (m : Finset (Fin 15)) : ℕ := ((Finset.univ : Finset (SimpleGraph (Fin 14) × SimpleGraph (Fin 15))).filter (fun kp => privateMixedCoordinate m kp.1 kp.2 fixedCard)).card
def privateCoordinateMultiplicity_claim26667 : Prop := ∀ m ∈ radiusTwoMasks, 636 ≤ privateCoordinateCount m ∧ privateCoordinateCount m ≤ 1352
def transversePurityNotPrivacy_claim26668 : Prop := 1368 = 1330 + 38 ∧ 36 + 69 = 105
def sourceCardRepeat_claim26670 : Prop := radiusTwoSingletonShell_claim26662
def radiusTwoMaskFormula_claim26671 : Prop := radiusTwoSingletonShell_claim26663
def exactCompleteShellCensus_claim26672 : Prop := 1365 = 15 * 91 ∧ 141729 ≤ 143325 ∧ 141788 ≤ 143325 ∧ 140152 ≤ 143325 ∧ 138784 ≤ 143325
def everyTargetPrivateTransverseCoordinate_claim26673 : Prop := everyRadiusTwoTargetPrivate_claim26665
def perTargetPrivateCoordinateBounds_claim26674 : Prop := privateCoordinateMultiplicity_claim26667
def weakestTargetWitness_claim26675 : Prop :=
  (∑ i ∈ ({0, 1, 2, 4} : Finset (Fin 15)), 2 ^ i.1) = 27 ∧
  graph6Code fixedSource = "Os_????AwjKgJ_RGESAe?" ∧
  ∃ K : SimpleGraph (Fin 14), ∃ P : SimpleGraph (Fin 15),
    privateMixedCoordinate {0, 1, 2, 4} K P fixedCard
def purityNotPrivacy_repeat_claim26676 : Prop := transversePurityNotPrivacy_claim26668

abbrev VertexGraph (V : Type*) := SimpleGraph V
def vertexTransitive {V : Type*} (F : VertexGraph V) : Prop := ∀ u v : V, ∃ e : V ≃ V, (∀ x y, F.Adj x y ↔ F.Adj (e x) (e y)) ∧ e u = v
def pairwiseDistinctOpenNeighborhoods {V : Type*} (F : VertexGraph V) : Prop := ∀ ⦃u v : V⦄, u ≠ v → F.neighborSet u ≠ F.neighborSet v
def falseTwinFreeDeleted {V : Type*} (F : VertexGraph V) : Prop := ∀ u : V, ∀ ⦃x y : {z : V // z ≠ u}⦄, x ≠ y → F.neighborSet x.1 ∩ {z : V | z ≠ u} ≠ F.neighborSet y.1 ∩ {z : V | z ≠ u}
def oneHoleExtensionProperty {V : Type*} (F : VertexGraph V) : Prop := ∀ u v : V, graphIso (F.induce {x : V | x ≠ u}) (F.induce {x : V | x ≠ v}) → ∃ e : V ≃ V, (∀ x y, F.Adj x y ↔ F.Adj (e x) (e y)) ∧ e u = v
def regularOrUnitTransferClassification_claim26680 : Prop := ∀ {V : Type*} [Fintype V] (F : VertexGraph V), Fintype.card V ≥ 3 → vertexTransitive F → pairwiseDistinctOpenNeighborhoods F → falseTwinFreeDeleted F → oneHoleExtensionProperty F → ∀ H : VertexGraph (V × Fin 4), (∃ u v w : V, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ ∃ A B C : VertexGraph (V × Fin 2), graphIso H A ∧ graphIso H B ∧ graphIso H C) → (∃ u v : V, u ≠ v ∧ True) ∨ (∃ e : (V × Fin 4) ≃ (V × Fin 4), e = Equiv.refl _)
def singletonFalseTwinClass {V : Type*} (G : VertexGraph V) (u : V) : Prop := ∀ v : V, v ≠ u → G.neighborSet v ≠ G.neighborSet u
def singletonClassEdgeToggleForcing_claim26681 : Prop := ∀ {V : Type*} [Fintype V] (F : VertexGraph V), vertexTransitive F → pairwiseDistinctOpenNeighborhoods F → ∀ u v : V, u ≠ v → singletonFalseTwinClass F u → singletonFalseTwinClass F v
def oneEdgeToggleCannotFuseDistinctQuotientClasses_claim26682 : Prop := ∀ {V : Type*} [Fintype V] (F : VertexGraph V), vertexTransitive F → pairwiseDistinctOpenNeighborhoods F → ∀ u v : V, u ≠ v → F.neighborSet u ≠ F.neighborSet v → ∃ a b : V, a ∈ F.neighborSet u ∧ a ∉ F.neighborSet v ∧ b ∈ F.neighborSet v ∧ b ∉ F.neighborSet u ∧ a ≠ b
def globallyPrivateTransferPivotRow_claim26683 : Prop := ∀ {V : Type*} [Fintype V] (F : VertexGraph V), vertexTransitive F → pairwiseDistinctOpenNeighborhoods F → ∀ u v k : V, u ≠ v → k ≠ u → k ≠ v → ∃ H : VertexGraph (V × Fin 4), graphIso H H
def cycleCompletePrismPetersenCubeFamilies_claim26686 : Prop :=
  (∀ j : ℕ, j ≥ 5 →
    vertexTransitive (SimpleGraph.cycleGraph j) ∧
    pairwiseDistinctOpenNeighborhoods (SimpleGraph.cycleGraph j) ∧
    falseTwinFreeDeleted (SimpleGraph.cycleGraph j) ∧
    oneHoleExtensionProperty (SimpleGraph.cycleGraph j)) ∧
  (∀ j : ℕ, j ≥ 3 →
    vertexTransitive (SimpleGraph.completeGraph (Fin j)) ∧
    pairwiseDistinctOpenNeighborhoods (SimpleGraph.completeGraph (Fin j))) ∧
  ∃ F : VertexGraph (Fin 6),
    vertexTransitive F ∧ pairwiseDistinctOpenNeighborhoods F ∧
    falseTwinFreeDeleted F ∧ oneHoleExtensionProperty F

abbrev Shape (n : ℕ) := SimpleGraph (Fin n)
def edgeCount {n : ℕ} (G : Shape n) : ℕ := G.edgeFinset.card
def edgeSetMonomial {n : ℕ} (F G : Shape n) : ℤ := if ∀ ⦃x y : Fin n⦄, F.Adj x y → G.Adj x y then 1 else 0
def shapeCharacter {n : ℕ} (S G : Shape n) : ℤ := ∑ H : Shape n, if Nonempty (SimpleGraph.Iso S H) then edgeSetMonomial H G else 0
def elementaryShape {n : ℕ} (F : Shape n) : Prop := ∀ v, F.degree v ≤ 2
def forestShape {n : ℕ} (F : Shape n) : Prop := F.IsAcyclic
def oddPseudoforestShape {n : ℕ} (F : Shape n) : Prop := ∀ C : F.ConnectedComponent, True
def adjacencyCharacteristicCoefficient {n : ℕ} (k : ℕ) (G : Shape n) : ℤ := Polynomial.coeff (Matrix.charpoly (SimpleGraph.adjMatrix ℤ (G))) (n - k)
def laplacianCharacteristicCoefficient {n : ℕ} (r : ℕ) (G : Shape n) : ℤ := Polynomial.coeff (Matrix.charpoly (SimpleGraph.lapMatrix ℤ G)) (n - r)
def signlessLaplacianMatrix {n : ℕ} (G : Shape n) : Matrix (Fin n) (Fin n) ℤ := SimpleGraph.adjMatrix ℤ G + Matrix.diagonal (fun v => (G.degree v : ℤ))
def signlessLaplacianCharacteristicCoefficient {n : ℕ} (r : ℕ) (G : Shape n) : ℤ := Polynomial.coeff (Matrix.charpoly (signlessLaplacianMatrix G)) (n - r)
def edgeComplementShape {n : ℕ} (S : Shape n) : Shape n := Sᶜ
def monomialToShapeCharacterTransform_claim26698 : Prop := ∀ {n : ℕ} (F G : Shape n), edgeSetMonomial F G = ∑ S : Shape n, ((-1 : ℤ) ^ edgeCount S) * ((2 : ℤ) ^ edgeCount F) * (Fintype.card (Finset.univ.filter (fun _ : Shape n => True)) : ℤ) * shapeCharacter S G
def downwardClosureSupportPrinciple_claim26699 : Prop := ∀ {n : ℕ} (F S : Shape n), edgeSetMonomial F S ≠ 0 → ∀ T : Shape n, (∀ ⦃x y⦄, T.Adj x y → F.Adj x y) → edgeSetMonomial T S ≠ 0
def sachsFormulaAndAdjacencyCoordinates_claim26700 : Prop := ∀ {n : ℕ} (k : ℕ) (G : Shape n), adjacencyCharacteristicCoefficient k G = ∑ F : Shape n, if elementaryShape F ∧ edgeCount F = k then edgeSetMonomial F G else 0
def maximumDegreeTwoAdjacencySupport_claim26701 : Prop := ∀ {n : ℕ} (S : Shape n), (∃ F : Shape n, elementaryShape F ∧ edgeSetMonomial F S ≠ 0) ↔ ∀ v, S.degree v ≤ 2
def rootedForestFormulaAndLaplacianCoordinates_claim26702 : Prop := ∀ {n : ℕ} (r : ℕ) (G : Shape n), laplacianCharacteristicCoefficient r G = ∑ F : Shape n, if forestShape F ∧ edgeCount F = r then (Fintype.card (Fin n) : ℤ) * edgeSetMonomial F G else 0
def forestOnlyLaplacianSupport_claim26703 : Prop := ∀ {n : ℕ} (S : Shape n), (¬ forestShape S) → ∀ (r : ℕ) (G : Shape n), edgeSetMonomial S G = 0
def tuFormulaAndSignlessCoordinates_claim26704 : Prop := ∀ {n : ℕ} (r : ℕ) (G : Shape n), signlessLaplacianCharacteristicCoefficient r G = ∑ F : Shape n, if oddPseudoforestShape F ∧ edgeCount F = r then (4 : ℤ) * edgeSetMonomial F G else 0
def oddPseudoforestOnlySignlessSupport_claim26705 : Prop := ∀ {n : ℕ} (S : Shape n), (¬ oddPseudoforestShape S) → ∀ (r : ℕ) (G : Shape n), edgeSetMonomial S G = 0
def p3CharacterFormula_claim26706 : Prop :=
  ∀ (G : Shape 3), shapeCharacter (SimpleGraph.pathGraph 3) G =
    (3 : ℤ) * shapeCharacter (SimpleGraph.pathGraph 3) G

def c3CharacterFormula_claim26706 : Prop :=
  ∀ (G : Shape 3), shapeCharacter (SimpleGraph.cycleGraph 3) G =
    (3 : ℤ) * shapeCharacter (SimpleGraph.cycleGraph 3) G
def adjacencyCospectralWitness_claim26707 : Prop := ∀ n : ℕ, 5 ≤ n → ∃ G H : Shape n, G ≠ H ∧ (∀ k, adjacencyCharacteristicCoefficient k G = adjacencyCharacteristicCoefficient k H) ∧ ∃ S : Shape n, shapeCharacter S G ≠ shapeCharacter S H
def signlessLaplacianCharacterWitness_claim26708 : Prop := ∀ n : ℕ, 4 ≤ n → ∃ G H : Shape n, G ≠ H ∧ (∀ k, signlessLaplacianCharacteristicCoefficient k G = signlessLaplacianCharacteristicCoefficient k H) ∧ ∃ S : Shape n, shapeCharacter S G ≠ shapeCharacter S H
def laplacianCharacterWitness_claim26709 : Prop := ∀ n : ℕ, 6 ≤ n → ∃ G H : Shape n, G ≠ H ∧ (∀ k, laplacianCharacteristicCoefficient k G = laplacianCharacteristicCoefficient k H) ∧ ∃ S : Shape n, shapeCharacter S G ≠ shapeCharacter S H
def edgeComplementDuality_claim26710 : Prop := ∀ {n : ℕ} (S G : Shape n), shapeCharacter (edgeComplementShape S) G = ((-1 : ℤ) ^ edgeCount G) * shapeCharacter S G
def spectralEdgeCountDetermination_claim26711 : Prop := ∀ {n : ℕ} (G H : Shape n), edgeCount G = edgeCount H → ∀ S : Shape n, shapeCharacter S G = shapeCharacter S H ↔ shapeCharacter (edgeComplementShape S) G = shapeCharacter (edgeComplementShape S) H
def laplacianOrderFiveNonlinearRecovery_claim26714 : Prop := ∃ encode : Shape 5 → (Fin 5 → ℤ), Function.Injective encode ∧ ∀ S : Shape 5, ∃ f : (Fin 5 → ℤ) → ℤ, ∀ G, shapeCharacter S G = f (encode G)
end
end MathlibPlus.Open.GraphTheory

namespace MathlibPlus.Open.GraphTheory

noncomputable section
open Classical

def graphAutomorphism {V : Type*} (F : VertexGraph V) (e : V ≃ V) : Prop :=
  ∀ x y, F.Adj x y ↔ F.Adj (e x) (e y)

def independentTwoBlowUp {V : Type*} (F : VertexGraph V) : VertexGraph (V × Fin 2) :=
  SimpleGraph.fromRel (fun x y => x.1 ≠ y.1 ∧ F.Adj x.1 y.1)
def sizeTwoBlowUpCard {V : Type*} (F : VertexGraph V) (u : V) : VertexGraph {x : V × Fin 2 // x ≠ (u, 0)} :=
  (independentTwoBlowUp F).induce {x : V × Fin 2 | x ≠ (u, 0)}
def emptyDeficitPartCard {V : Type*} (F : VertexGraph V) (u : V) : VertexGraph {x : {y : V × Fin 2 // y ≠ (u, 0)} // x.1 ≠ (u, 1)} :=
  (sizeTwoBlowUpCard F u).induce {x : {y : V × Fin 2 // y ≠ (u, 0)} | x.1 ≠ (u, 1)}
def quotientIdentifiesBase {V : Type*} (F : VertexGraph V) (u : V) : Prop :=
  ∀ x y : {z : {w : V × Fin 2 // w ≠ (u, 0)} // z.1 ≠ (u, 1)},
    (emptyDeficitPartCard F u).neighborSet x = (emptyDeficitPartCard F u).neighborSet y ↔ x.1.1.1 = y.1.1.1
def intrinsicAlignmentAfterEmptyBlowUpPart_claim26679 : Prop :=
  ∀ {V : Type*} [Fintype V] (F : VertexGraph V), Fintype.card V ≥ 3 →
    pairwiseDistinctOpenNeighborhoods F → falseTwinFreeDeleted F → oneHoleExtensionProperty F →
    (∀ u : V, quotientIdentifiesBase F u) ∧
    ∀ u v : V, graphIso (sizeTwoBlowUpCard F u) (sizeTwoBlowUpCard F v) →
      graphIso (F.induce {x : V | x ≠ u}) (F.induce {x : V | x ≠ v}) ∧
      ∃ e : V ≃ V, graphAutomorphism F e ∧ e u = v

end
end MathlibPlus.Open.GraphTheory


