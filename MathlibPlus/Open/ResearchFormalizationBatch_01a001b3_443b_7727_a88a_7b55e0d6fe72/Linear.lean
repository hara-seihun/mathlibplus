import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a001b3_443b_7727_a88a_7b55e0d6fe72

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Rows belonging to a selected collection of row blocks. -/
def rowOver {R B : Type} [Fintype R] [DecidableEq B]
    (block : R → B) (bs : Finset B) : Type :=
  {r : R // block r ∈ bs}

def columnOver {V : Type} [Fintype V] (S C : Finset V) : Type :=
  {v : V // v ∈ S ∧ v ∈ C}

instance instFintypeRowOver {R B : Type} [Fintype R] [DecidableEq B]
    (block : R → B) (bs : Finset B) : Fintype (rowOver block bs) :=
  Fintype.subtype (Finset.univ.filter (fun r : R => block r ∈ bs)) (by simp)

instance instFintypeColumnOver {V : Type} [Fintype V]
    (S C : Finset V) : Fintype (columnOver S C) :=
  Fintype.subtype (Finset.univ.filter (fun v : V => v ∈ S ∧ v ∈ C)) (by simp)

/-- The bipartite incidence graph of the block-sparse presentation. -/
def blockSparseIncidenceGraph {R V B : Type} [Fintype R] [Fintype V]
    [DecidableEq R] [DecidableEq V] [DecidableEq B]
    (M : Matrix R V ℚ) (block : R → B) : SimpleGraph (B ⊕ V) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ b : B, ∃ v : V,
      e = Sym2.mk (Sum.inl b) (Sum.inr v) ∧
        ∃ r : R, block r = b ∧ M r v ≠ 0}

/-- Rank of the matrix restricted to selected row blocks and columns. -/
def restrictedRank {F R V B : Type} [Field F] [Fintype R] [Fintype V]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (bs : Finset B) (S C : Finset V) : ℕ :=
  Module.finrank F
    (Submodule.span F
      (Set.range
        (fun v : columnOver S C =>
          fun r : rowOver block bs => M r.1 v.1)))

def blockRank {F R V B : Type} [Field F] [Fintype R] [Fintype V]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (b : B) (S : Finset V) : ℕ :=
  restrictedRank M block {b} S Finset.univ

def incidentBlock {F R V B : Type} [Zero F] [Fintype R]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (b : B) (v : V) : Prop :=
  ∃ r : R, block r = b ∧ M r v ≠ 0

def blockExposedAt {F R V B : Type} [Field F] [Fintype R] [Fintype V]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (b : B) (S : Finset V) (v : V) : Prop :=
  v ∈ S ∧ blockRank M block b S > blockRank M block b (S.erase v)

def blockExposed {F R V B : Type} [Field F] [Fintype R] [Fintype V]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S : Finset V) (v : V) : Prop :=
  ∃ b : B, incidentBlock M block b v ∧ blockExposedAt M block b S v

def blockStalled {F R V B : Type} [Field F] [Fintype R] [Fintype V]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S : Finset V) : Prop :=
  ∀ v ∈ S, ¬ blockExposed M block S v

def blockDeletionRemaining {V : Type} [DecidableEq V]
    (S : Finset V) (order : List V) : Finset V :=
  order.foldl (fun T v => T.erase v) S

def validBlockDeletion {F R V B : Type} [Field F] [Fintype R] [Fintype V]
    [DecidableEq B] [DecidableEq V] (M : Matrix R V F) (block : R → B)
    (S : Finset V) : List V → Prop
  | [] => blockStalled M block S
  | v :: order =>
      v ∈ S ∧ blockExposed M block S v ∧
        validBlockDeletion M block (S.erase v) order

def atomicCoreProperty {F R V B : Type} [Field F] [Fintype R] [Fintype V]
    [DecidableEq B] [DecidableEq V] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) : Prop :=
  (∀ order : List V,
    validBlockDeletion M block Finset.univ order →
      blockDeletionRemaining Finset.univ order = S₀) ∧
    blockStalled M block S₀ ∧
    (∀ T : Finset V, blockStalled M block T → T ⊆ S₀)

/-- Atomic deletion is confluent and exposure survives deletion of other columns. -/
def claim5153 : Prop :=
  ∀ (F R V B : Type) [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq R] [DecidableEq V] [DecidableEq B]
    (M : Matrix R V F) (block : R → B),
    (∀ (S T : Finset V) (v : V) (b : B),
      T ⊆ S → v ∈ T → blockExposedAt M block b S v →
        blockExposedAt M block b T v) ∧
      ∃! S₀ : Finset V, atomicCoreProperty M block S₀

/-- Frozen radius-r column balls and their row-block side. -/
def incidentBlocks {F R V B : Type} [Zero F] [Fintype R] [Fintype B]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (v : V) : Finset B := by
  classical
  exact Finset.univ.filter (fun b => incidentBlock M block b v)

def columnNeighbors {F R V B : Type} [Zero F] [Fintype R] [Fintype B]
    [DecidableEq B] [DecidableEq V] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (v : V) : Finset V := by
  classical
  exact S₀.filter (fun w =>
    ∃ b : B, incidentBlock M block b v ∧ incidentBlock M block b w)

def radiusColumns {F R V B : Type} [Zero F] [Fintype R] [Fintype B]
    [DecidableEq B] [DecidableEq V] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (v : V) : ℕ → Finset V
  | 0 => {v}
  | r + 1 =>
      radiusColumns M block S₀ v r ∪
        (radiusColumns M block S₀ v r).biUnion
          (fun w => columnNeighbors M block S₀ w)

def radiusBlocks {F R V B : Type} [Zero F] [Fintype R] [Fintype B]
    [DecidableEq B] [DecidableEq V] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (v : V) : ℕ → Finset B
  | 0 => ∅
  | r + 1 =>
      radiusBlocks M block S₀ v r ∪
        (radiusColumns M block S₀ v r).biUnion
          (fun w => incidentBlocks M block w)

def radiusRank {F R V B : Type} [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (v : V) (r : ℕ) (S : Finset V) : ℕ :=
  restrictedRank M block (radiusBlocks M block S₀ v r) S
    (radiusColumns M block S₀ v r)

def radiusExposedCondition {F R V B : Type} [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (r : ℕ) (S : Finset V) (v : V) : Prop :=
  v ∈ S ∧ S ⊆ S₀ ∧
    radiusRank M block S₀ v r S >
      radiusRank M block S₀ v r (S.erase v)

def radiusCertificate {F R V B : Type} [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (r : ℕ) (S : Finset V) (v : V) : Prop :=
  ∃ coeff : rowOver block (radiusBlocks M block S₀ v r) → F,
    ∀ w : columnOver S (radiusColumns M block S₀ v r),
      (∑ q : rowOver block (radiusBlocks M block S₀ v r),
        coeff q * M q.1 w.1) =
        if w.1 = v then 1 else 0

/-- Radius exposure is exactly the local coordinate-functional certificate. -/
def claim5155 : Prop :=
  ∀ (F R V B : Type) [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq R] [DecidableEq V] [DecidableEq B]
    (M : Matrix R V F) (block : R → B)
    (S₀ S : Finset V) (v : V) (r : ℕ),
    atomicCoreProperty M block S₀ → S ⊆ S₀ → v ∈ S →
      (v ∈ S ∧ S ⊆ S₀ ∧
        radiusRank M block S₀ v r S >
          radiusRank M block S₀ v r (S.erase v)) ↔
        radiusCertificate M block S₀ r S v

def radiusStalled {F R V B : Type} [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (r : ℕ) (S : Finset V) : Prop :=
  S ⊆ S₀ ∧ ∀ v ∈ S, ¬ radiusExposedCondition M block S₀ r S v

def validRadiusDeletion {F R V B : Type} [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (r : ℕ) (S : Finset V) : List V → Prop
  | [] => radiusStalled M block S₀ r S
  | v :: order =>
      v ∈ S ∧ radiusExposedCondition M block S₀ r S v ∧
        validRadiusDeletion M block S₀ r (S.erase v) order

def radiusCoreProperty {F R V B : Type} [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] (M : Matrix R V F) (block : R → B)
    (S₀ : Finset V) (r : ℕ) (Core : Finset V) : Prop :=
  (∀ order : List V,
    validRadiusDeletion M block S₀ r S₀ order →
      blockDeletionRemaining S₀ order = Core) ∧
    radiusStalled M block S₀ r Core ∧
    (∀ T : Finset V, radiusStalled M block S₀ r T → T ⊆ Core)

/-- Frozen-ball deletion is monotone and has a canonical stopping core. -/
def claim5156 : Prop :=
  ∀ (F R V B : Type) [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq R] [DecidableEq V] [DecidableEq B]
    (M : Matrix R V F) (block : R → B) (S₀ : Finset V),
    atomicCoreProperty M block S₀ →
      ∀ r : ℕ,
        (∀ (S T : Finset V) (v : V),
          T ⊆ S → v ∈ T →
            radiusExposedCondition M block S₀ r S v →
              radiusExposedCondition M block S₀ r T v) ∧
          ∃! Core : Finset V, radiusCoreProperty M block S₀ r Core

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a001b3_443b_7727_a88a_7b55e0d6fe72
