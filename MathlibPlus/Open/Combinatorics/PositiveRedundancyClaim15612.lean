import MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.PositiveRedundancy

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The finite carrier of unlabeled twelve-vertex tree types. -/
abbrev TreeType12 :=
  {T : MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd.GraphClass //
    T ∈ MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd.treeTypeSet14336 12}

/-- A proper graph motif is a finite graph with no isolated vertices. -/
def noIsolated {m : ℕ} (G : SimpleGraph (Fin m)) : Prop :=
  ∀ v, ∃ w, G.Adj v w

abbrev GraphMotif :=
  Σ m : ℕ, {G : SimpleGraph (Fin m) // noIsolated G}

open MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

/-- A representative of a finite graph class, retaining its actual finite carrier. -/
noncomputable def representativeGraph (T : TreeType12) :
    SimpleGraph (Quot.out T.1).1 :=
  (Quot.out T.1).2.2

/-- The target edge count at the analysed level. -/
noncomputable def targetEdgeCount (T : TreeType12) : ℕ :=
  Nat.card (representativeGraph T).edgeSet

/-- The target edge set, used as the finite cover universe. -/
noncomputable def targetEdges (T : TreeType12) :
    Finset (Sym2 (Quot.out T.1).1) := by
  let q := Quot.out T.1
  letI : Fintype q.1 := q.2.1
  letI : Fintype q.2.2.edgeSet := Fintype.ofFinite _
  exact q.2.2.edgeFinset

/-- The actual edge count of a graph motif. -/
noncomputable def motifEdgeCount (F : GraphMotif) : ℕ :=
  Nat.card F.2.1.edgeSet

/-- The total incidence excess over the eleven target edges. -/
def redundancy {k : ℕ} (F : Fin k → GraphMotif) : ℤ :=
  (∑ i : Fin k, (motifEdgeCount (F i) : ℤ)) - 11

/-- Images of the ordered motifs as actual subgraphs of the target. -/
def coverEmbedding {k : ℕ} (F : Fin k → GraphMotif) (T : TreeType12) :=
  {S : Fin k → (representativeGraph T).Subgraph //
    ∀ i, Nonempty ((F i).2.1 ≃g (S i).coe)}

/-- Joint edge coverage; no disjointness condition is imposed, so overlaps remain. -/
def jointlyCovers {k : ℕ} (F : Fin k → GraphMotif) (T : TreeType12)
    (S : coverEmbedding F T) : Prop :=
  ∀ e ∈ targetEdges T, ∃ i, e ∈ (S.1 i).edgeSet

/-- The ordered Kocay cover tuples for a fixed family and target. -/
def coveringEmbeddings {k : ℕ} (F : Fin k → GraphMotif) (T : TreeType12) :=
  {S : coverEmbedding F T // jointlyCovers F T S}

/-- The usual Kocay count of jointly edge-covering motif images. -/
noncomputable def coverCount {k : ℕ} (F : Fin k → GraphMotif) (T : TreeType12) : ℕ :=
  Nat.card (coveringEmbeddings F T)

/-- The integer row entry used in pairings with the integer tree vector. -/
def coverRow {k : ℕ} (F : Fin k → GraphMotif) (T : TreeType12) : ℤ :=
  coverCount F T

/-- Proper families have every motif spanning fewer than twelve vertices. -/
def properFamily {k : ℕ} (F : Fin k → GraphMotif) : Prop :=
  ∀ i, (F i).1 < 12

/-- The redundancy-zero ordered-partition layer. -/
def partitionFamily {k : ℕ} (F : Fin k → GraphMotif) : Prop :=
  properFamily F ∧ redundancy F = 0

/-- A genuine redundancy-one covering family. -/
def redundancyOneFamily {k : ℕ} (F : Fin k → GraphMotif) : Prop :=
  properFamily F ∧ redundancy F = 1

/-- An integer vector invisible to every same-level ordered-partition row. -/
def partitionKernel (w : TreeType12 → ℤ) : Prop :=
  ∀ {k : ℕ} (F : Fin k → GraphMotif), partitionFamily F →
    ∑ T : TreeType12, w T * coverRow F T = 0

/-- The exact order-twelve relation: support and coefficient data are retained. -/
def exactKernelVector (w : TreeType12 → ℤ) : Prop :=
  w ≠ 0 ∧
    Fintype.card TreeType12 = 551 ∧
    (∀ T : TreeType12, targetEdgeCount T = 11) ∧
    Fintype.card {T : TreeType12 // w T ≠ 0} = 105 ∧
    (∀ T, w T ≠ 0 →
      Int.natAbs (w T) = 1 ∨ Int.natAbs (w T) = 2 ∨ Int.natAbs (w T) = 3) ∧
    partitionKernel w ∧
    (∀ v : TreeType12 → ℤ, partitionKernel v →
      ∃ a : ℤ, v = a • w)

/--
Claim 15612: a genuine cover row with one repeated edge detects the exact
redundancy-zero tree relation.  The statement deliberately makes no claim
about other edge levels or about a uniform completion-redundancy bound.
-/
def positiveRedundancyDetectsRelation_claim15612 : Prop :=
  ∃ w : TreeType12 → ℤ,
    exactKernelVector w ∧
      ∃ (k : ℕ) (F : Fin k → GraphMotif),
        redundancyOneFamily F ∧
          ∑ T : TreeType12, w T * coverRow F T ≠ 0

end
end MathlibPlus.Open.Combinatorics.PositiveRedundancy
