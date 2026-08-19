import MathlibPlus.Open.ResearchFormalization.R2015InterpolationAndRelaxation

namespace MathlibPlus.Open.ResearchFormalization.R2778Claim35804

open MathlibPlus.Open.ResearchFormalization.Batch01
open MathlibPlus.Open.ResearchFormalization.R2015InterpolationAndRelaxation
open Filter Topology

noncomputable section

noncomputable def recordSixDegreeMomentInequalities35804
    (d : ℕ → ℕ) : Prop :=
  ∀ n k : ℕ, k ≤ n →
    ((Nat.choose (d n) k : ℝ) /
      (Nat.choose n k : ℝ)) ≤ alpha k

noncomputable def erdos86AsymptoticHalfBound35804
    (d : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (d n : ℝ) / (n : ℝ) ≤ (1 / 2 : ℝ) + ε

noncomputable def recordSixOnlyDerivation35804 : Prop :=
  ∀ d : ℕ → ℕ,
    recordSixDegreeMomentInequalities35804 d →
      erdos86AsymptoticHalfBound35804 d

/-- Record-6 degree moments alone admit the fixed floor-3/5 model, so they do
not imply the Erdos-86 asymptotic half bound.  The countermodel retains no
translated support placement or cross-K coupling data. -/
def degreeMomentNonImplication_claim35804 : Prop :=
  ¬ recordSixOnlyDerivation35804 ∧
    recordSixDegreeMomentInequalities35804 constantDegreeLaw ∧
    Filter.Tendsto
      (fun n : ℕ => (constantDegreeLaw n : ℝ) / (n : ℝ))
      atTop (nhds ((3 : ℝ) / 5)) ∧
    ¬ erdos86AsymptoticHalfBound35804 constantDegreeLaw ∧
    (1 : ℝ) / 2 < 3 / 5

end

end MathlibPlus.Open.ResearchFormalization.R2778Claim35804
