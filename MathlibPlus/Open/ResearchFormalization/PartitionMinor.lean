import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open scoped BigOperators

/-- A finite preimage-labelled partition-minor state.  The blocks themselves
are the original-cell preimage labels. -/
def PartitionMinorState (S : Type*) := Finset S × Finset (Finset S)

def singletonPartition {S : Type*} (T : Finset S) : Finset (Finset S) := by
  classical
  exact T.image (fun e => ({e} : Finset S))

def initialPartitionMinorState {S : Type*} [Fintype S] : PartitionMinorState S := by
  classical
  exact (Finset.univ, singletonPartition (Finset.univ : Finset S))

def isPartitionOf {S : Type*} (P : Finset (Finset S)) (T : Finset S) : Prop := by
  classical
  exact
    (∀ B ∈ P, B.Nonempty ∧ B ⊆ T) ∧
      ∀ e ∈ T, ∃! B : Finset S, B ∈ P ∧ e ∈ B

def wellFormedMinorState {S : Type*} (s : PartitionMinorState S) : Prop :=
  s.1.Nonempty ∧ isPartitionOf s.2 s.1

def scalarCircuitHypotheses {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (lambda : S → ℚ) : Prop :=
  (∀ e, 0 < lambda e) ∧
    (Finset.sum Finset.univ (fun e => lambda e) = 1) ∧
    (Finset.sum Finset.univ (fun e => (lambda e) • ell e) = 0)

def deletedSpan {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (T : Finset S) : Submodule ℚ W := by
  classical
  exact Submodule.span ℚ {w | ∃ e : S, e ∉ T ∧ w = ell e}

abbrev quotientSpace {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (T : Finset S) :=
  W ⧸ deletedSpan ell T

def quotientClass {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (T : Finset S) (e : S) :
    quotientSpace ell T :=
  Submodule.Quotient.mk (p := deletedSpan ell T) (ell e)

def blockTotal {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (lambda : S → ℚ)
    (T B : Finset S) : quotientSpace ell T :=
  Finset.sum B (fun e => (lambda e) • quotientClass ell T e)

def terminalPreimageLabel {S : Type*} (B : Finset S) : Finset S := B

/-- The positive scalar-circuit starts at the singleton preimage partition. -/
def claim51605 : Prop :=
  ∀ (S W : Type*) (_ : Fintype S) (_ : AddCommGroup W) (_ : Module ℚ W)
    (ell : S → W) (lambda : S → ℚ),
    scalarCircuitHypotheses ell lambda →
      initialPartitionMinorState (S := S) =
        (Finset.univ, singletonPartition (Finset.univ : Finset S))

/-- State data, quotient classes, block totals, and retained preimage labels. -/
def claim51607 : Prop :=
  ∀ (S W : Type*) (_ : Fintype S) (_ : AddCommGroup W) (_ : Module ℚ W)
    (ell : S → W) (lambda : S → ℚ) (T : Finset S) (P : Finset (Finset S)),
    scalarCircuitHypotheses ell lambda →
    T.Nonempty → T ⊆ (Finset.univ : Finset S) → isPartitionOf P T →
      (∀ e : S, quotientClass ell T e =
        Submodule.Quotient.mk (p := deletedSpan ell T) (ell e)) ∧
      (∀ B, B ∈ P →
        blockTotal ell lambda T B =
          Finset.sum B (fun e => (lambda e) • quotientClass ell T e)) ∧
      (∀ B, B ∈ P → terminalPreimageLabel B = B)

def coarsens {S : Type*} (T : Finset S)
    (P Q : Finset (Finset S)) : Prop :=
  isPartitionOf P T ∧ isPartitionOf Q T ∧
    ∀ B ∈ P, ∃ C ∈ Q, B ⊆ C

def coarsenState {S : Type*} (T : Finset S)
    (_P Q : Finset (Finset S)) : PartitionMinorState S :=
  (T, Q)

def subblocks {S : Type*} (P : Finset (Finset S)) (C : Finset S) :
    Finset (Finset S) := by
  classical
  exact P.filter (fun B => B ⊆ C)

/-- Coarsening keeps the support and adds the old block totals. -/
def claim51608 : Prop :=
  ∀ (S W : Type*) (_ : Fintype S) (_ : AddCommGroup W) (_ : Module ℚ W)
    (ell : S → W) (lambda : S → ℚ) (T : Finset S)
    (P Q : Finset (Finset S)),
    scalarCircuitHypotheses ell lambda → coarsens T P Q →
      coarsenState T P Q = (T, Q) ∧
      ∀ C ∈ Q,
        blockTotal ell lambda T C =
          Finset.sum (subblocks P C) (fun B => blockTotal ell lambda T B)

def blocksUnion {S : Type*} (A : Finset (Finset S)) : Finset S := by
  classical
  exact A.biUnion id

def isSubcollection {S : Type*}
    (A P : Finset (Finset S)) : Prop :=
  A.Nonempty ∧ ∀ B ∈ A, B ∈ P

def contractState {S : Type*} (_T : Finset S)
    (_P A : Finset (Finset S)) : PartitionMinorState S :=
  (blocksUnion A, A)

def minorStep {S : Type*} (s t : PartitionMinorState S) : Prop :=
  wellFormedMinorState s ∧
    ((∃ Q : Finset (Finset S),
        coarsens s.1 s.2 Q ∧ t = coarsenState s.1 s.2 Q) ∨
      (∃ A : Finset (Finset S),
        isSubcollection A s.2 ∧ t = contractState s.1 s.2 A))

def reachableMinorState {S : Type*} [Fintype S]
    (s : PartitionMinorState S) : Prop :=
  Relation.ReflTransGen minorStep (initialPartitionMinorState (S := S)) s

/-- Every coarsening/contraction program retains a nonempty partition of its
surviving support. -/
def claim51612 : Prop :=
  ∀ (S W : Type*) (_ : Fintype S) (_ : AddCommGroup W) (_ : Module ℚ W)
    (ell : S → W) (lambda : S → ℚ),
    scalarCircuitHypotheses ell lambda →
      ∀ s : PartitionMinorState S, reachableMinorState s → wellFormedMinorState s

def contractInitialTo {S : Type*} [Fintype S]
    (T : Finset S) : PartitionMinorState S :=
  contractState (Finset.univ : Finset S) (singletonPartition (Finset.univ : Finset S))
    (singletonPartition T)

def contractThenAggregate {S : Type*} [Fintype S]
    (T : Finset S) (P : Finset (Finset S)) : PartitionMinorState S :=
  coarsenState (contractInitialTo T).1 (contractInitialTo T).2 P

/-- Every finite program has the unique two-step preimage-labelled normal form. -/
def claim51614 : Prop :=
  ∀ (S W : Type*) (_ : Fintype S) (_ : AddCommGroup W) (_ : Module ℚ W)
    (ell : S → W) (lambda : S → ℚ),
    scalarCircuitHypotheses ell lambda →
      ∀ s : PartitionMinorState S, reachableMinorState s →
        ∃! (T : Finset S),
          ∃! (P : Finset (Finset S)),
            T.Nonempty ∧ isPartitionOf P T ∧
              s = contractThenAggregate T P

/-- Every partition-minor pair is reachable by one singleton contraction and
one aggregation. -/
def claim51617 : Prop :=
  ∀ (S : Type*) (_ : Fintype S) (T : Finset S) (P : Finset (Finset S)),
    T.Nonempty → isPartitionOf P T →
      reachableMinorState (T, P)

abbrev blockIndex {S : Type*} (P : Finset (Finset S)) :=
  {B : Finset S // B ∈ P}

def indexedBlockTotal {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (lambda : S → ℚ)
    (T : Finset S) (P : Finset (Finset S)) (i : blockIndex P) :
    quotientSpace ell T :=
  blockTotal ell lambda T i.1

def blockSpan {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (lambda : S → ℚ)
    (T : Finset S) (P : Finset (Finset S)) :
    Submodule ℚ (quotientSpace ell T) := by
  classical
  exact Submodule.span ℚ (Set.range (indexedBlockTotal ell lambda T P))

def completeBlockRelation {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (lambda : S → ℚ)
    (T : Finset S) (P : Finset (Finset S)) : Prop := by
  classical
  exact ∀ c : blockIndex P → ℚ,
    Finset.sum Finset.univ (fun i => c i • indexedBlockTotal ell lambda T P i) = 0 ↔
      ∃ q : ℚ, ∀ i, c i = q

/-- The terminal block totals have only the all-ones relation and span a
space of dimension one less than the number of blocks. -/
def claim51619 : Prop :=
  ∀ (S W : Type*) (_ : Fintype S) (_ : AddCommGroup W) (_ : Module ℚ W)
    (ell : S → W) (lambda : S → ℚ) (T : Finset S) (P : Finset (Finset S)),
    scalarCircuitHypotheses ell lambda → T.Nonempty → isPartitionOf P T →
      (Finset.sum Finset.univ
          (fun i : blockIndex P => indexedBlockTotal ell lambda T P i) = 0) ∧
      completeBlockRelation ell lambda T P ∧
      Module.finrank ℚ (blockSpan ell lambda T P) = P.card - 1

def properBlockSum {S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℚ W] (ell : S → W) (lambda : S → ℚ)
    (T : Finset S) (A : Finset (Finset S)) : quotientSpace ell T :=
  Finset.sum A (fun B => blockTotal ell lambda T B)

/-- Unary terminals vanish, while every proper nonempty union of at least two
terminal blocks is nonzero. -/
def claim51620 : Prop :=
  ∀ (S W : Type*) (_ : Fintype S) (_ : AddCommGroup W) (_ : Module ℚ W)
    (ell : S → W) (lambda : S → ℚ) (T : Finset S) (P : Finset (Finset S)),
    scalarCircuitHypotheses ell lambda → T.Nonempty → isPartitionOf P T →
      (P.card = 1 → ∀ B ∈ P, blockTotal ell lambda T B = 0) ∧
      (2 ≤ P.card →
        (∀ B ∈ P, blockTotal ell lambda T B ≠ 0) ∧
        ∀ A : Finset (Finset S), A ⊆ P → A.Nonempty → A ≠ P →
          properBlockSum ell lambda T A ≠ 0)

end

end MathlibPlus.Open.ResearchFormalization
