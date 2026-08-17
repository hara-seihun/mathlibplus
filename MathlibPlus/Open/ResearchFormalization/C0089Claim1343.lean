import MathlibPlus.Open.Analysis.SuffixOptimizers
import MathlibPlus.Open.ResearchFormalization.C0089

namespace MathlibPlus.Open.ResearchFormalization.C0089Claim1343

open MathlibPlus.Open.Analysis
open MathlibPlus.Open.ResearchFormalization.C0089

noncomputable section

/-- The strict full-half-line bound used in the least-start predicate. -/
def validFrom (c X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x →
    primeCounting x < x / (Real.log x - 1 - c / Real.log x)

/-- Least integer start for the displayed real half-line predicate. -/
def leastIntegerStart (c : ℝ) (N : ℕ) : Prop :=
  validFrom c (N : ℝ) ∧
    ∀ M : ℕ, M < N → ¬ validFrom c (M : ℝ)

/-- The suffix maximum value, represented by the supremum of the exact score
image on the real suffix. -/
noncomputable def alpha (N : ℕ) : ℝ :=
  sSup (B '' Set.Ici (N : ℝ))

/-- The predecessor endpoint of the coefficient cell. -/
def beta (N : ℕ) : ℝ :=
  B ((N : ℝ) - 1)

/-- The supremum in `alpha` is a genuine maximum on the suffix. -/
def suffixMaximumAttained (N : ℕ) (a : ℝ) : Prop :=
  ∃ x₀ : ℝ,
    (N : ℝ) ≤ x₀ ∧ B x₀ = a ∧
      ∀ x : ℝ, (N : ℝ) ≤ x → B x ≤ a

def supplementaryRow : ℚ × ℕ :=
  ((114900031 : ℚ) / 100000000, 42575222481)

def allRows : List (ℚ × ℕ) := correctedRows ++ [supplementaryRow]

/-- Claim 1343: the half-open coefficient cell is classified for every real
coefficient below the predecessor logarithmic threshold, and every displayed
coefficient is strictly interior to its cell. -/
def uniformFortyThreeCellClassification_claim1343 : Prop :=
  ∀ row : ℚ × ℕ, row ∈ allRows →
    let N : ℕ := row.2
    let c₀ : ℝ := (row.1 : ℝ)
    suffixMaximumAttained N (alpha N) ∧
      (∀ c : ℝ,
        c < Real.log ((N : ℝ) - 1) *
            (Real.log ((N : ℝ) - 1) - 1) →
          (leastIntegerStart c N ↔
            alpha N < c ∧ c ≤ beta N)) ∧
      alpha N < c₀ ∧ c₀ < beta N

end

end MathlibPlus.Open.ResearchFormalization.C0089Claim1343
