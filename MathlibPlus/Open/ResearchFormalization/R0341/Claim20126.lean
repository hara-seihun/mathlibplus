import MathlibPlus.Open.ResearchFormalization.R0341.Claim20128

namespace MathlibPlus.Open.ResearchFormalization.R0341.Claim20126

noncomputable section

open Classical
open MathlibPlus.Open.ResearchFormalization.R0341.Claim20128

/-- The rank of the generic stack after restricting its columns to a finite
subset of `E`.  The stack parameter is shifted because the reviewed carrier
uses `Fin (k + 1)` for its `k + 1` observable blocks. -/
private noncomputable def genericRankOnSubset
    {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (k : ℕ) (S : Finset E) : ℕ :=
  Matrix.rank
    ((genericDiagonalStack L (k - 1)).submatrix
      (fun r => r) (fun e : S => e.1))

/-- The finite minimum over all column subsets of `S`, written using `sInf`
so its nonempty finite carrier remains explicit without a proof-bearing
helper definition. -/
private noncomputable def genericRankMinimum
    {F R E : Type*} [Field F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (k : ℕ) (S : Finset E) : ℕ :=
  sInf {m : ℕ |
    ∃ X : Finset E, X ⊆ S ∧
      m = (S \ X).card + k * columnRank L X}

/-- Claim 20126: the generic diagonal stack has the exact minimum rank formula
on every finite column subset. -/
def claim20126 : Prop :=
  ∀ (F R E : Type*) [Field F] [Infinite F]
    [Fintype R] [Fintype E] [DecidableEq E]
    (L : Matrix R E F) (k : ℕ) (_hk : 0 < k) (S : Finset E),
    genericRankOnSubset L k S = genericRankMinimum L k S

end

end MathlibPlus.Open.ResearchFormalization.R0341.Claim20126
