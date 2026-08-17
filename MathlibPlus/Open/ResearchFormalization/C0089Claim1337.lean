import MathlibPlus.Open.Analysis.SuffixOptimizers
import MathlibPlus.Open.ResearchFormalization.C0089

namespace MathlibPlus.Open.ResearchFormalization.C0089Claim1337

open MathlibPlus.Open.Analysis
open MathlibPlus.Open.ResearchFormalization.C0089

noncomputable section

/-- The exact strict bound on a real half-line. -/
def validFrom (c X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x →
    primeCounting x < x / (Real.log x - 1 - c / Real.log x)

/-- A natural start is least when no smaller natural start is valid. -/
def leastIntegerStart (c : ℝ) (N : ℕ) : Prop :=
  validFrom c (N : ℝ) ∧
    ∀ M : ℕ, M < N → ¬ validFrom c (M : ℝ)

/-- The usual nontrivial-factor definition of a composite natural. -/
def compositeNatural (N : ℕ) : Prop :=
  ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = N

/-- A final equality is the unique score crossing in the predecessor unit
interval. -/
def finalRealEquality (c : ℝ) (N : ℕ) : Prop :=
  ∃! x : ℝ,
    (N : ℝ) - 1 < x ∧ x < (N : ℝ) ∧ B x = c

def supplementaryRow : ℚ × ℕ :=
  ((114900031 : ℚ) / 100000000, 42575222481)

def allRows : List (ℚ × ℕ) := correctedRows ++ [supplementaryRow]

/-- Claim 1337: every corrected Table 9 row and the supplementary repair has
its full real half-line, least displayed start, composite start, and unique
final real equality. -/
def correctedCompleteTable9HalfLines_claim1337 : Prop :=
  (∀ row ∈ correctedRows,
    validFrom (row.1 : ℝ) (row.2 : ℝ) ∧
      leastIntegerStart (row.1 : ℝ) row.2 ∧
      compositeNatural row.2 ∧
      finalRealEquality (row.1 : ℝ) row.2) ∧
    validFrom ((114900031 : ℝ) / 100000000) 42575222481 ∧
    leastIntegerStart ((114900031 : ℝ) / 100000000) 42575222481 ∧
    compositeNatural 42575222481 ∧
    finalRealEquality ((114900031 : ℝ) / 100000000) 42575222481

end

end MathlibPlus.Open.ResearchFormalization.C0089Claim1337
