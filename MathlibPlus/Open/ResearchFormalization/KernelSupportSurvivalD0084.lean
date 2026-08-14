import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Rows selected by a set of blocks in the given block partition. -/
def rowsInBlocks {R B : Type*} [Fintype R] (rowBlock : R → B)
    (blocks : Finset B) : Finset R :=
  Finset.univ.filter (fun i => rowBlock i ∈ blocks)

/-- A row certificate for the coordinate functional at a surviving column. -/
def rowCoordinateCertificate {𝔽 R V : Type*} [Field 𝔽] [Fintype R]
    (M : Matrix R V 𝔽) (rows : Finset R) (columns : Finset V) (v : V) : Prop :=
  ∃ c : R → 𝔽,
    (∀ i, i ∉ rows → c i = 0) ∧
      (∀ u, u ∈ columns →
        (∑ i : R, c i * M i u) = if u = v then 1 else 0)

/-- Block exposure, using the row-certificate formulation of the rank comparison. -/
def blockExposed {𝔽 R V B : Type*} [Field 𝔽] [Fintype R]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (columns : Finset V) (v : V) : Prop :=
  v ∈ columns ∧
    ∃ b : B,
      rowCoordinateCertificate M (rowsInBlocks rowBlock {b}) columns v

/-- One simultaneous atomic peeling round. -/
def atomicPeelRound {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (columns : Finset V) : Finset V :=
  columns.filter (fun v => ¬ ∃ b : B,
    rowCoordinateCertificate M (rowsInBlocks rowBlock {b}) columns v)

/-- A finite iteration of atomic peeling. -/
def iterateAtomicPeeling {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) : Nat → Finset V → Finset V
  | 0, columns => columns
  | n + 1, columns =>
      iterateAtomicPeeling M rowBlock n (atomicPeelRound M rowBlock columns)

/-- The terminal set of the atomic block-exposure peeling. -/
def atomicCore {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) : Finset V :=
  iterateAtomicPeeling M rowBlock (Fintype.card V + 1) Finset.univ

/-- Incidence in the bipartite graph induced by the atomic core. -/
def coreBlockIncident {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V) (b : B) (v : V) : Prop :=
  v ∈ core ∧ ∃ i : R, rowBlock i = b ∧ M i v ≠ 0

/-- One column-to-column step in that incidence graph. -/
def coreColumnStep {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V) (u v : V) : Prop :=
  u ∈ core ∧ v ∈ core ∧
    ∃ b : B,
      coreBlockIncident M rowBlock core b u ∧
        coreBlockIncident M rowBlock core b v

/-- Reachability by exactly `n` column-to-column steps. -/
def coreColumnReach {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V) :
    Nat → V → V → Prop
  | 0, v, u => u = v
  | n + 1, v, u =>
      ∃ w, coreColumnReach M rowBlock core n v w ∧
        coreColumnStep M rowBlock core w u

/-- Columns in the frozen radius-`r` ball around a core column. -/
def radiusColumnBall {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (v : V) : Finset V :=
  Finset.univ.filter (fun u => ∃ n : Nat, n ≤ r ∧
    coreColumnReach M rowBlock core n v u)

/-- Blocks on the row side of the frozen radius-`r` ball. -/
def radiusBlockBall {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (v : V) : Finset B :=
  Finset.univ.filter (fun b => ∃ n : Nat, n < r ∧ ∃ u,
    coreColumnReach M rowBlock core n v u ∧
      coreBlockIncident M rowBlock core b u)

/-- Radius exposure in the frozen ball, again via a row certificate. -/
def radiusExposed {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (columns : Finset V) (v : V) : Prop :=
  columns ⊆ core ∧ v ∈ columns ∧
    ∃ c : R → 𝔽,
      (∀ i, i ∉ rowsInBlocks rowBlock
        (radiusBlockBall M rowBlock core r v) → c i = 0) ∧
        (∀ u, u ∈ columns →
          u ∈ radiusColumnBall M rowBlock core r v →
            (∑ i : R, c i * M i u) = if u = v then 1 else 0)

/-- One simultaneous radius-exposure peeling round. -/
def radiusPeelRound {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r : Nat) (columns : Finset V) : Finset V :=
  columns.filter (fun v => ¬ radiusExposed M rowBlock core r columns v)

/-- A finite iteration of frozen-radius peeling. -/
def iterateRadiusPeeling {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V) (r : Nat) :
    Nat → Finset V → Finset V
  | 0, columns => columns
  | n + 1, columns =>
      iterateRadiusPeeling M rowBlock core r n
        (radiusPeelRound M rowBlock core r columns)

/-- The terminal set of the frozen radius-`r` peeling. -/
def radiusCore {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (r : Nat) : Finset V :=
  iterateRadiusPeeling M rowBlock (atomicCore M rowBlock) r
    (Fintype.card V + 1) (atomicCore M rowBlock)

/-- Exposure with a certificate using at most `k` blocks in the frozen ball. -/
def radiusWidthExposed {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r k : Nat) (columns : Finset V) (v : V) : Prop :=
  columns ⊆ core ∧ v ∈ columns ∧
    ∃ blocks : Finset B,
      blocks ⊆ radiusBlockBall M rowBlock core r v ∧ blocks.card ≤ k ∧
        ∃ c : R → 𝔽,
          (∀ i, i ∉ rowsInBlocks rowBlock blocks → c i = 0) ∧
            (∀ u, u ∈ columns →
              u ∈ radiusColumnBall M rowBlock core r v →
                (∑ i : R, c i * M i u) = if u = v then 1 else 0)

/-- One simultaneous radius-width peeling round. -/
def radiusWidthPeelRound {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r k : Nat) (columns : Finset V) : Finset V :=
  columns.filter (fun v => ¬ radiusWidthExposed M rowBlock core r k columns v)

/-- A finite iteration of frozen-radius width peeling. -/
def iterateRadiusWidthPeeling {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (core : Finset V)
    (r k : Nat) : Nat → Finset V → Finset V
  | 0, columns => columns
  | n + 1, columns =>
      iterateRadiusWidthPeeling M rowBlock core r k n
        (radiusWidthPeelRound M rowBlock core r k columns)

/-- The terminal radius-width core `Core_(r,k)`. -/
def radiusWidthCore {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) (r k : Nat) : Finset V :=
  iterateRadiusWidthPeeling M rowBlock (atomicCore M rowBlock) r k
    (Fintype.card V + 1) (atomicCore M rowBlock)

/--
Kernel support survives the atomic, frozen-radius, and radius-width local
contractions of a block-sparse matrix.  The first conjunct records the local
non-exposure assertion for every surviving column set containing the kernel
support; the remaining conjuncts record the resulting core inclusions.
-/
def kernelSupportSurvivesLocalContractions
    {𝔽 R V B : Type*} [Field 𝔽] [Fintype R] [Fintype V] [Fintype B]
    (M : Matrix R V 𝔽) (rowBlock : R → B) : Prop :=
  ∀ x : V → 𝔽, Matrix.mulVec M x = 0 →
    ∀ v : V, x v ≠ 0 →
      (∀ columns : Finset V,
        (∀ u, x u ≠ 0 → u ∈ columns) → v ∈ columns →
          (∀ b : B,
            ¬ rowCoordinateCertificate M (rowsInBlocks rowBlock {b}) columns v) ∧
          (∀ r : Nat,
            ¬ radiusExposed M rowBlock (atomicCore M rowBlock) r columns v) ∧
          (∀ r k : Nat, 1 ≤ k →
            ¬ radiusWidthExposed M rowBlock (atomicCore M rowBlock) r k columns v)) ∧
      v ∈ atomicCore M rowBlock ∧
      (∀ r : Nat, v ∈ radiusCore M rowBlock r) ∧
      (∀ r k : Nat, 1 ≤ k → v ∈ radiusWidthCore M rowBlock r k)

end
end MathlibPlus.Open.ResearchFormalization
