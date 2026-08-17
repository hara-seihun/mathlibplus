import MathlibPlus.Open.Analysis.ResearchFormalizeR0438

open Filter
open scoped BigOperators Topology

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0521.Claim22286

/-- The normalized dense-tail gap used by the finite-radius profile. -/
def denseTailGap (q ε : ℝ) (i : ℤ) : ℝ :=
  (ε + q ^ Int.natAbs i) / (1 + ε)

/-- The finite-radius constant, as the supremum of the displayed finite set. -/
noncomputable def muR (R : ℕ) (q : ℝ) : ℝ :=
  sSup {c : ℝ |
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ R ∧
      c = (q ^ (-(j : ℤ)) + q ^ j - 2) / (j : ℝ) ^ 2}

/-- Claim 22286: the explicit finite-radius profile constant vanishes as q rises to one. -/
def claim22286 : Prop :=
  ∀ R : ℕ, 1 ≤ R →
    Tendsto (fun q : ℝ => muR R q)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (𝓝 0) ∧
    ∀ η : ℝ, 0 < η →
      ∃ q : ℝ,
        0 < q ∧ q < 1 ∧ muR R q < η ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ (k : ℤ) (j : ℕ), 1 ≤ j → j ≤ R →
              denseTailGap q ε (k - (j : ℤ)) +
                  denseTailGap q ε (k + (j : ℤ)) -
                2 * denseTailGap q ε k ≤
                muR R q * denseTailGap q ε k * (j : ℝ) ^ 2

end MathlibPlus.Open.ResearchFormalization.R0521.Claim22286
