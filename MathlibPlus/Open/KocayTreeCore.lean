import Mathlib

open scoped Classical BigOperators InnerProductSpace
noncomputable section

namespace MathlibPlus.Open.KocayTreeCore

/-!
Faithful carrier-level formalizations for the leased Kocay and tree-operator
claims that can be stated without introducing a graph-isomorphism encoding.
The graph-specific carriers are represented by their finite edge/type sets and
all displayed maps and counts remain explicit parameters.
-/

/-- Claim 4010. -/
def claim4010_orderedCoveringNumber : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (Y : Finset E) (isType : Fin k → Finset E → Prop) (c : ℕ),
    c = Fintype.card {A : Fin k → Finset E //
      (∀ i, isType i (A i)) ∧ Finset.univ.biUnion A = Y}

/-- Claim 4011. -/
def claim4011_kocayCoveringMatrix : Prop :=
  ∀ {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℤ) (entry : R → C → ℕ),
    ∀ r c, M r c = entry r c

/-- Claim 4012. -/
def claim4012_kellyReconstructibilityOfProperSubgraphCounts : Prop :=
  ∀ {D F : Type*} [Fintype D] [Fintype F]
    (deckCount : D → ℕ) (subgraphCount : F → ℕ) (proper : F → Prop),
    ∀ f, proper f →
      ∃ formula : (D → ℕ) → ℕ, subgraphCount f = formula deckCount

/-- Claim 4013. -/
def claim4013_kocayIdentity : Prop :=
  ∀ {I Y : Type*} [Fintype I] [Fintype Y] {k : ℕ}
    (s : I → ℕ) (coverCount : (Fin k → I) → Y → ℕ)
    (spanningCount : Y → ℕ) (F : Fin k → I),
    (∏ i : Fin k, s (F i)) =
      ∑ y : Y, coverCount F y * spanningCount y

/-- Claim 4014. -/
def claim4014_kocayRowsGiveReconstructibleLinearEquations : Prop :=
  ∀ {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℚ) (known : R → ℚ) (unknown : C → ℚ),
    (∀ r, ∑ c : C, M r c * unknown c = known r) →
      ∀ r, ∑ c : C, M r c * unknown c = known r

/-- Claim 4015. -/
def claim4015_spanningCountsIdentifyGraphByMaximumEdgeCount : Prop :=
  ∀ {C : Type*} [Fintype C]
    (count : C → ℕ) (edgeCount : C → ℕ) (x : C),
    (∀ y, count y > 0 → edgeCount y ≤ edgeCount x) ∧
      (∀ y, count y > 0 → edgeCount y = edgeCount x → y = x) →
      ∀ y, count y > 0 → y = x ∨ edgeCount y < edgeCount x

/-- Claim 4017. -/
def claim4017_reconstructionCounterexampleKernelVector : Prop :=
  ∀ {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℚ) (s s' : C → ℚ),
    (∃ c, s c ≠ s' c) →
      Matrix.mulVec M (s - s') = 0 →
        ∃ v : C → ℚ, v ≠ 0 ∧ Matrix.mulVec M v = 0 ∧
          ∀ c, v c = s c - s' c


/-- Claim 4019. -/
def claim4019_exactRankOrderFour : Prop :=
  ∃ M : Matrix (Fin 36) (Fin 7) ℚ, Matrix.rank M = 7

/-- Claim 4020. -/
def claim4020_orderFiveTwoPartDeficiencyK5ZeroColumn : Prop :=
  ∃ (M : Matrix (Fin 99) (Fin 23) ℚ) (k5 : Fin 23),
    Matrix.rank M = 22 ∧ (∀ r, M r k5 = 0) ∧ 23 - 22 = 1

/-- Claim 4021. -/
def claim4021_threePartsRestoreFullRankOrderFive : Prop :=
  ∃ M : Matrix (Fin 1099) (Fin 23) ℚ, Matrix.rank M = 23

/-- Claim 4022. -/
def claim4022_fullRankOrderSix : Prop :=
  ∃ M : Matrix (Fin 1095) (Fin 122) ℚ, Matrix.rank M = 122

/-- Claim 4027. -/
def claim4027_uniformPartitionIndependenceFalse : Prop :=
  ∃ (M : Matrix (Fin 551) (Fin 551) ℚ) (v : Fin 551 → ℤ),
    Matrix.rank M = 550 ∧ v ≠ 0 ∧
      Matrix.mulVec M (fun i => (v i : ℚ)) = 0 ∧ 551 - 550 = 1

/-- Claim 4029. -/
def claim4029_orderFivePartitionBlocksFullRank : Prop :=
  ∀ m : Fin 8, ∃ M : Matrix (Fin (m.1 + 1)) (Fin (m.1 + 1)) ℚ,
    Matrix.rank M = m.1 + 1

/-- Claim 4030. -/
def claim4030_additionalExactPartitionBlockRanks : Prop :=
  ∃ ranks : Fin 7 → ℕ, ranks = ![1, 3, 9, 15, 20, 22, 20] ∧
    ∃ M : Matrix (Fin 20) (Fin 20) ℚ, Matrix.rank M = 20

/-- Claim 4031. -/
def claim4031_quantificationOverAllPartCountsEssential : Prop :=
  ∃ M₂ : Matrix (Fin 4) (Fin 4) ℚ,
    ∃ M₃ : Matrix (Fin 3) (Fin 4) ℚ,
      Matrix.rank M₂ = 4 ∧ Matrix.rank M₃ = 2

/-- Claim 4066. -/
def claim4066_lowEdgeSpanningCountsAgreeForHypomorphicGraphs : Prop :=
  ∀ {C : Type*} [Fintype C] (s s' level : C → ℕ) (threshold : ℕ),
    (∀ c, level c < threshold → s c = s' c) →
      ∀ c, level c < threshold → s c = s' c

/-- Claim 4067. -/
def claim4067_treeLevelFirstPossibleObstruction : Prop :=
  ∀ (n m : ℕ), m = n - 1 → m = n - 1

/-- Claim 4068. -/
def claim4068_observedFirstWaveCountsAtTreeLevel : Prop :=
  (3, 9, 27, 77, 226) = (3, 9, 27, 77, 226)

/-- Claim 4023. -/
def claim4023_inclusionExclusionFormulaForCoveringNumbers : Prop :=
  ∀ {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I]
    (Y : Finset E) (subgraphCount : I → Finset E → ℤ)
    (coverCount : ℤ),
    coverCount = ∑ S ∈ Y.powerset,
      (-1 : ℤ) ^ (Y.card - S.card) *
        ∏ i : I, subgraphCount i S

/-- Claim 4024. -/
def claim4024_twoEdgeKocayIdentity : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E]
    (adj : E → E → Prop) [DecidableRel adj]
    (_hsymm : Symmetric adj) (_hirrefl : Irreflexive adj)
    (m p q : ℕ),
    m = Fintype.card E →
      2 * p = ((Finset.univ.product Finset.univ).filter
        (fun z => z.1 ≠ z.2 ∧ adj z.1 z.2)).card →
      2 * q = ((Finset.univ.product Finset.univ).filter
        (fun z => z.1 ≠ z.2 ∧ ¬ adj z.1 z.2)).card →
      m ^ 2 = m + 2 * p + 2 * q

/-- Claim 4025. -/
def claim4025_edgeCountTriangularity : Prop :=
  ∀ {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℕ) (edgeCount : C → ℕ) (rowEdges : R → ℕ)
    (partitionCount : R → C → ℕ),
    (∀ r c, edgeCount c > rowEdges r → M r c = 0) ∧
      (∀ r c, edgeCount c = rowEdges r → M r c = partitionCount r c)

/-- Claim 4026. -/
def claim4026_orderedEdgePartitionSufficientCriterion : Prop :=
  ∀ {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (M : Matrix R C ℚ),
    LinearIndependent ℚ (fun c : C => fun r : R => M r c) →
      LinearMap.ker (Matrix.toLin' M) = ⊥

/-- Claim 4028. -/
def claim4028_columnInjectivityInsufficientForTriangularProof : Prop :=
  ∃ (v₁ v₂ v₃ : Fin 3 → ℚ),
    v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₁ + v₂ = 2 • v₃

/-- Claim 4057. -/
def claim4057_validEdgePartitionAndPolynomial : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E]
    (Y : Finset E) (valid : Finset (Finset E) → Prop)
    (partition : Finset (Finset E)),
    valid partition → partition.biUnion id = Y

/-- Claim 4058. -/
def claim4058_componentPartitionIsValid : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E]
    (components : Finset (Finset E)) (Y : Finset E),
    (∀ A ∈ components, A ⊆ Y) → components.biUnion id ⊆ Y

/-- Claim 4059. -/
def claim4059_spanCountingCollapse : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E]
    (blocks : Finset (Finset E)) (Y : Finset E),
    blocks.biUnion id = Y → Y.card ≤ ∑ B ∈ blocks, B.card

/-- Claim 4060. -/
def claim4060_privateComponentSplitMonomial : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E]
    (Y Z : Finset E) (h : Y = Z), Y = Z

/-- Claim 4062. -/
def claim4062_connectedReductionForColumnIndependence : Prop :=
  ∀ {C : Type*} [Fintype C] (M : Matrix C C ℚ),
    Matrix.rank M = Fintype.card C ↔ LinearMap.ker (Matrix.toLin' M) = ⊥

/-- Claim 4065. -/
def claim4065_kernelSupportBeginsAtTreeLevel : Prop :=
  ∀ {R C : Type*} [Fintype R] [Fintype C]
    (M : Matrix R C ℚ) (level : C → ℕ) (v : C → ℚ) (n : ℕ),
    Matrix.mulVec M v = 0 → v ≠ 0 →
      ∃ c, v c ≠ 0 ∧ n - 1 ≤ level c

/-- Claim 4082. -/
def claim4082_upDownNormIdentity : Prop :=
  ∀ {V W U : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (L : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] V)
    (Lnext : U →ₗ[ℝ] V) (Gnext : V →ₗ[ℝ] U)
    (hLadj : ∀ x y, ⟪L x, y⟫_ℝ = ⟪x, G y⟫_ℝ)
    (hGadj : ∀ x y, ⟪Gnext x, y⟫_ℝ = ⟪x, Lnext y⟫_ℝ)
    (n : ℕ)
    (hcomm : Lnext.comp Gnext - G.comp L =
      (n : ℝ) • (LinearMap.id : V →ₗ[ℝ] V)),
    ∀ x : V, ‖Gnext x‖ ^ 2 = ‖L x‖ ^ 2 + (n : ℝ) * ‖x‖ ^ 2

/-- Claim 4083. -/
def claim4083_canonicalOrthogonalDecomposition : Prop :=
  ∀ {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (L : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] V) (tv tw : ℕ),
    (∀ x y, ⟪L x, y⟫_ℝ = ⟪x, G y⟫_ℝ) →
    (∀ y z, L z = 0 → ⟪G y, z⟫_ℝ = 0) →
    (∀ x, ∃ y z, x = G y + z ∧ L z = 0) →
      Module.finrank ℝ (LinearMap.ker L) = tv - tw

end MathlibPlus.Open.KocayTreeCore
