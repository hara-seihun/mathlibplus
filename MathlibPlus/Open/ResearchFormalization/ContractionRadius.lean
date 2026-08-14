import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def matrixRestrictedColumn
    {𝔽 Row Col : Type*} [Field 𝔽] [DecidableEq Row]
    (M : Matrix Row Col 𝔽) (rows : Finset Row) (c : Col) : Row → 𝔽 :=
  fun i => if i ∈ rows then M i c else 0

noncomputable def matrixBlockRank
    {𝔽 Row Col : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rows : Finset Row) (cols : Finset Col) : ℕ :=
  Module.finrank 𝔽
    (Submodule.span 𝔽
      (Set.image (fun c : Col => matrixRestrictedColumn M rows c)
        (↑cols : Set Col)))

noncomputable def rowsOfBlock
    {Row Block : Type*} [Fintype Row] [DecidableEq Row]
    (rowBlock : Row → Block) (b : Block) : Finset Row := by
  classical
  exact Finset.univ.filter (fun i => rowBlock i = b)

noncomputable def blockIncident
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (b : Block) (v : Col) : Prop :=
  ∃ i, rowBlock i = b ∧ M i v ≠ 0

noncomputable def blockExposed
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (S : Finset Col) (v : Col) : Prop := by
  classical
  exact
    v ∈ S ∧ ∃ b,
      matrixBlockRank M (rowsOfBlock rowBlock b) S >
        matrixBlockRank M (rowsOfBlock rowBlock b) (S.erase v)

noncomputable def blockDeletionState
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block) : ℕ → Finset Col
  | 0 => Finset.univ
  | n + 1 => by
      classical
      exact
        (blockDeletionState M rowBlock n).filter
          (fun v => ¬ blockExposed M rowBlock (blockDeletionState M rowBlock n) v)

noncomputable def atomicCore
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block) : Finset Col :=
  blockDeletionState M rowBlock (Fintype.card Col)

noncomputable def columnStep
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (C : Finset Col) (v w : Col) : Prop :=
  v ∈ C ∧ w ∈ C ∧ ∃ b,
    blockIncident M rowBlock b v ∧ blockIncident M rowBlock b w

noncomputable def columnReach
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block) (C : Finset Col) :
    ℕ → Col → Col → Prop
  | 0, v, w => v = w
  | n + 1, v, w => ∃ u,
      columnReach M rowBlock C n v u ∧ columnStep M rowBlock C u w

noncomputable def radiusBallColumns
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (C : Finset Col) (r : ℕ) (v : Col) : Finset Col := by
  classical
  exact Finset.univ.filter (fun w => ∃ n ≤ r,
    columnReach M rowBlock C n v w)

noncomputable def radiusBallRows
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (C : Finset Col) (r : ℕ) (v : Col) : Finset Row := by
  classical
  exact Finset.univ.filter (fun i => ∃ n < r, ∃ w,
    columnReach M rowBlock C n v w ∧
      blockIncident M rowBlock (rowBlock i) w)

noncomputable def radiusExposed
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (C S : Finset Col) (r : ℕ) (v : Col) : Prop :=
  v ∈ S ∧
    matrixBlockRank M (radiusBallRows M rowBlock C r v)
      (S ∩ radiusBallColumns M rowBlock C r v) >
    matrixBlockRank M (radiusBallRows M rowBlock C r v)
      ((S.erase v) ∩ radiusBallColumns M rowBlock C r v)

noncomputable def radiusDeletionState
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (C : Finset Col) (r : ℕ) : ℕ → Finset Col
  | 0 => C
  | n + 1 => by
      classical
      exact
        (radiusDeletionState M rowBlock C r n).filter
          (fun v => ¬ radiusExposed M rowBlock C
            (radiusDeletionState M rowBlock C r n) r v)

noncomputable def coreAtRadius
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block) (r : ℕ) : Finset Col :=
  radiusDeletionState M rowBlock (atomicCore M rowBlock) r (Fintype.card Col)

noncomputable def parallelDeletionWave
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block)
    (r n : ℕ) : Finset Col :=
  radiusDeletionState M rowBlock (atomicCore M rowBlock) r n \
    radiusDeletionState M rowBlock (atomicCore M rowBlock) r (n + 1)

noncomputable def dismantlingDepth
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block) (r : ℕ) : ℕ := by
  classical
  exact
    ((Finset.range (Fintype.card Col)).filter
      (fun n => (parallelDeletionWave M rowBlock r n).Nonempty)).card

noncomputable def contractionRadius
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block) : WithTop ℕ := by
  classical
  exact sInf (Set.image (fun r : ℕ => (r : WithTop ℕ))
    {r : ℕ | 1 ≤ r ∧ coreAtRadius M rowBlock r = ∅})

def matroidalContractionRadiusAndDismantlingDepth
    {𝔽 Row Col Block : Type*} [Field 𝔽] [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M : Matrix Row Col 𝔽) (rowBlock : Row → Block) : Prop := by
  classical
  exact
    contractionRadius M rowBlock =
        (if h : ∃ r : ℕ, 1 ≤ r ∧ coreAtRadius M rowBlock r = ∅ then
          (Nat.find h : WithTop ℕ)
        else ⊤) ∧
      ∀ r : ℕ,
        dismantlingDepth M rowBlock r =
          ((Finset.range (Fintype.card Col)).filter
            (fun n => (parallelDeletionWave M rowBlock r n).Nonempty)).card

end MathlibPlus.Open.ResearchFormalization
