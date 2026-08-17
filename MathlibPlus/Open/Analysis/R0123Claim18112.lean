import MathlibPlus.Analysis.BernsteinCellMoments
import MathlibPlus.Analysis.Claim18111

namespace MathlibPlus.Open.ResearchFormalization.R0123

/-- Claim 18112: the reviewed Bernstein cell-moment kernel is strictly
 totally positive for positive ordered cell indices and all ordered natural
 moment indices, including the m=0 column. -/
def strictTotalPositivityR_18112 : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (n : Fin r → ℕ+) (m : Fin r → ℕ),
      StrictMono n → StrictMono m →
        0 < Matrix.det (fun i j =>
          MathlibPlus.Analysis.BernsteinCellMoments.bernsteinCellMomentCoefficient
            (n i) (m j))

end MathlibPlus.Open.ResearchFormalization.R0123
