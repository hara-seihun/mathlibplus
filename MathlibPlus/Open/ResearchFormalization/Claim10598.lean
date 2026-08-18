import MathlibPlus.Open.ResearchFormalization.FormalizationBatch01a006da

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

/-- Claim 10598: the four positive rational atoms give strict positivity of
all available weighted-Vandermonde minors, while their exact completed
rank-two and rank-three quantities have opposite signs. -/
def claim10598 : Prop :=
  let x : Fin 4 → ℝ := ![(1 / 100 : ℝ), 1, 2, 3]
  let w : Fin 4 → ℝ := ![(11 : ℝ), 10, 1 / 100, 1 / 100]
  let B : Fin 4 → Fin 6 → ℝ := fun i j => w i * x i ^ j.val
  let m : ℕ → ℝ := fun j => ∑ i : Fin 4, w i * x i ^ j
  (24 + 90 + 80 + 15 = 209) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      ∀ rows : Fin k → Fin 4, StrictMono rows →
        ∀ exponents : Fin k → Fin 6, StrictMono exponents →
          0 < Matrix.det
            (fun i j : Fin k => B (rows i) (exponents j))) ∧
    m 0 = 1051 / 50 ∧
    m 1 = 254 / 25 ∧
    m 2 = 101311 / 10000 ∧
    m 3 = 10350011 / 1000000 ∧
    m 4 = 1097000011 / 100000000 ∧
    m 5 = 127500000011 / 10000000000 ∧
    0 < completedBezoutRankTwoQuantity m ∧
    completedBezoutRankTwoQuantity m = 1858050996109 / 2500000000 ∧
    completedBezoutRankThreeQuantity m =
      -4942242941740486966119673885039 /
        31250000000000000000000 ∧
    completedBezoutRankThreeQuantity m < 0

end

end MathlibPlus.Open.ResearchFormalization
