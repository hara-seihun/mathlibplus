import MathlibPlus.Open.ResearchFormalization.R3630

namespace MathlibPlus.Open.ResearchFormalization.R3630

noncomputable section

open scoped BigOperators

/-- Covariance of two real targets after conditioning on a finite transcript cell. -/
noncomputable def realConditionalCovariance {n : ℕ}
    (f g : RademacherCube n → ℝ)
    (cell : Finset (RademacherCube n)) : ℝ :=
  let μf := realConditionalMean f cell
  let μg := realConditionalMean g cell
  cell.sum (fun x => (f x - μf) * (g x - μg)) / (cell.card : ℝ)

/-- The mixture expectation of conditional covariance with a fixed target. -/
def lawExpectedConditionalCovariance {n : ℕ} (law : BooleanLaw n)
    (z : RademacherCube n → ℝ)
    (cell : Finset (RademacherCube n)) : ℝ :=
  (law.map (fun entry =>
    entry.2 * realConditionalCovariance entry.1.1 z cell)).sum

/-- Claim 51069: a finite Boolean mixture has an edge-2-Lipschitz mean, and
its current posterior variance is bounded by the expected component area and
then by the expected component query cost, with the same chain on every
positive-probability transcript cell. -/
def claim51069_survivingUnconditionalCovarianceConsequence : Prop :=
  ∀ (n : ℕ) (g : RademacherCube n → ℝ) (law : BooleanLaw n),
    representsTarget g law →
      lipPlus g ≤ 1 ∧
      cubeCovariance g g = lawExpectedCovariance law g ∧
      cubeCovariance g g ≤ lawExpectedArea law ∧
      lawExpectedArea law ≤ lawExpectedQueryCost law ∧
      (∀ (tree : DecisionTree n) (path : List Bool),
        0 < (transcriptCell tree path).card →
          realConditionalVariance g (transcriptCell tree path) =
              realConditionalCovariance g g (transcriptCell tree path) ∧
            realConditionalCovariance g g (transcriptCell tree path) =
              lawExpectedConditionalCovariance law g (transcriptCell tree path) ∧
            lawExpectedConditionalCovariance law g (transcriptCell tree path) ≤
              lawExpectedArea law ∧
            lawExpectedArea law ≤ lawExpectedQueryCost law)

end

end MathlibPlus.Open.ResearchFormalization.R3630
