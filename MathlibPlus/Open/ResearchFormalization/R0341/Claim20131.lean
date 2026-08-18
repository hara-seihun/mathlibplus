import MathlibPlus.Open.ResearchFormalization.R0341.Claim20128

namespace MathlibPlus.Open.ResearchFormalization.R0341.Claim20131

noncomputable section

open Classical
open MathlibPlus.Open.ResearchFormalization.R0341.Claim20128

/-- Claim 20131: a proper column subset can violate the k-fold rank condition
although the whole column set passes the naive dimension count; the resulting
generic-stack rank is strictly below the whole-set minimum formula. -/
def claim20131 : Prop :=
  ∃ (F R E : Type*) (_ : Field F) (_ : Infinite F)
    (_ : Fintype R) (_ : Fintype E) (_ : DecidableEq E)
    (L : Matrix R E F) (k : ℕ) (_hk : 0 < k) (X : Finset E),
    X ⊂ (Finset.univ : Finset E) ∧
      X.card > k * columnRank L X ∧
      (Finset.univ : Finset E).card ≤
        k * columnRank L (Finset.univ : Finset E) ∧
      Matrix.rank (genericDiagonalStack L (k - 1)) <
        min ((Finset.univ : Finset E).card)
          (k * columnRank L (Finset.univ : Finset E))

end

end MathlibPlus.Open.ResearchFormalization.R0341.Claim20131
