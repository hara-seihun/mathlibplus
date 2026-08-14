import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- The row-block/column incidence relation of a block-sparse matrix. -/
def blockSparseIncidenceGraph
    {𝔽 R B V : Type*} [Field 𝔽]
    (M : Matrix R V 𝔽) (rowBlock : R → B) :
    (B ⊕ V) → (B ⊕ V) → Prop
  | Sum.inl b, Sum.inr v => ∃ r, rowBlock r = b ∧ M r v ≠ 0
  | Sum.inr v, Sum.inl b => ∃ r, rowBlock r = b ∧ M r v ≠ 0
  | _, _ => False

/-- A finite attachment card as described by its finite vertex type and
finite neighbor set at each vertex. -/
structure FiniteAttachmentCard where
  V : Type
  finiteV : Fintype V
  neighbors : V → Finset V

def attachmentDegree (C : FiniteAttachmentCard) (v : C.V) : ℕ :=
  (C.neighbors v).card

def curvature (C : FiniteAttachmentCard) (v : C.V) : ℤ :=
  2 - (attachmentDegree C v : ℤ)

/-- The degree-sign assertions for Euler curvature. -/
def curvatureSignsByDegree : Prop :=
  ∀ (C : FiniteAttachmentCard) (v : C.V),
    (attachmentDegree C v = 1 → curvature C v = 1) ∧
    (attachmentDegree C v = 2 → curvature C v = 0) ∧
    (attachmentDegree C v = 3 → curvature C v = -1) ∧
    (3 ≤ attachmentDegree C v → curvature C v < 0)

/-- The adjacency action on the curvature channel. -/
def curvatureTransportChannel (C : FiniteAttachmentCard) (v : C.V) : ℤ :=
  ∑ x ∈ C.neighbors v, (2 - (attachmentDegree C x : ℤ))

def originalDegreeChannel (C : FiniteAttachmentCard) : C.V → ℤ :=
  fun v => attachmentDegree C v

def originalBinomialChannel (C : FiniteAttachmentCard) : C.V → ℤ :=
  fun v => Nat.choose (attachmentDegree C v) 2

def originalNeighborMomentChannel (C : FiniteAttachmentCard) : C.V → ℤ :=
  fun v => ∑ x ∈ C.neighbors v, ((attachmentDegree C x : ℤ) - 1)

/-- The four original second-attachment-jet channels. -/
def originalSecondAttachmentJet (C : FiniteAttachmentCard) : Set (C.V → ℤ) :=
  {fun _ => 1,
    originalDegreeChannel C,
    originalBinomialChannel C,
    originalNeighborMomentChannel C}

def degreeIn (K : Type*) [Field K]
    (C : FiniteAttachmentCard) (v : C.V) : K :=
  attachmentDegree C v

def curvatureIn (K : Type*) [Field K]
    (C : FiniteAttachmentCard) (v : C.V) : K :=
  2 - degreeIn K C v

def transportIn (K : Type*) [Field K]
    (C : FiniteAttachmentCard) (v : C.V) : K :=
  ∑ x ∈ C.neighbors v, curvatureIn K C x

/-- The original four channels after extension of scalars to a field. -/
def originalKChannels (K : Type*) [Field K]
    (C : FiniteAttachmentCard) : Fin 4 → C.V → K :=
  ![fun _ => 1,
    degreeIn K C,
    fun v => Nat.choose (attachmentDegree C v) 2,
    fun v => ∑ x ∈ C.neighbors v, (degreeIn K C x - 1)]

/-- The constant, Euler-curvature, squared-curvature, and transported-curvature
channels after extension of scalars to a field. -/
def curvatureKChannels (K : Type*) [Field K]
    (C : FiniteAttachmentCard) : Fin 4 → C.V → K :=
  ![fun _ => 1,
    curvatureIn K C,
    fun v => (curvatureIn K C v) ^ 2,
    transportIn K C]

/-- Equality of the spans of the original and Euler-curvature four-channel jets. -/
def channelChangeMatrix (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
    2, -1, 0, 0;
    4, -3, 2, 0;
    0, 1, 0, -1]

def spanEquivalenceAwayFromTwo : Prop :=
  ∀ (K : Type*) [Field K], (2 : K) ≠ 0 →
    (Matrix.det (channelChangeMatrix K) ≠ 0 ∧
      ∀ (C : FiniteAttachmentCard),
        (∀ v : C.V,
          (fun i => curvatureKChannels K C i v) =
            (channelChangeMatrix K).mulVec (fun i => originalKChannels K C i v)) ∧
        Submodule.span K (Set.range (originalKChannels K C)) =
          Submodule.span K (Set.range (curvatureKChannels K C)))

/-- A finite tree carrier for the subcubic transport formula. -/
structure FiniteAttachmentTree where
  V : Type
  finiteV : Fintype V
  adjacency : SimpleGraph V

noncomputable def treeNeighbors (C : FiniteAttachmentTree) (v : C.V) : Finset C.V :=
  letI := C.finiteV
  letI := (Set.toFinite (C.adjacency.neighborSet v)).fintype
  C.adjacency.neighborFinset v

noncomputable def treeDegree (C : FiniteAttachmentTree) (v : C.V) : ℕ :=
  letI := C.finiteV
  letI := (Set.toFinite (C.adjacency.neighborSet v)).fintype
  C.adjacency.degree v

noncomputable def treeCurvature (C : FiniteAttachmentTree) (v : C.V) : ℤ :=
  2 - (treeDegree C v : ℤ)

noncomputable def treeTransport (C : FiniteAttachmentTree) (v : C.V) : ℤ :=
  ∑ x ∈ treeNeighbors C v, treeCurvature C x

noncomputable def leafNeighborCount (C : FiniteAttachmentTree) (v : C.V) : ℕ :=
  (treeNeighbors C v).filter (fun x => treeDegree C x = 1) |>.card

noncomputable def degreeThreeNeighborCount (C : FiniteAttachmentTree) (v : C.V) : ℕ :=
  (treeNeighbors C v).filter (fun x => treeDegree C x = 3) |>.card

/-- The subcubic curvature-transport formula on a finite tree. -/
def subcubicTransportFormula : Prop :=
  ∀ (C : FiniteAttachmentTree), C.adjacency.IsTree →
    (∀ x : C.V,
      treeDegree C x = 1 ∨ treeDegree C x = 2 ∨ treeDegree C x = 3) →
    ∀ v : C.V,
      treeTransport C v =
        (leafNeighborCount C v : ℤ) - (degreeThreeNeighborCount C v : ℤ)

end MathlibPlus.Open.ResearchFormalization
