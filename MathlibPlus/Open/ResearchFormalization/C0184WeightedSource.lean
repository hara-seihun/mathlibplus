import Mathlib
import MathlibPlus.Open.ResearchFormalization.C0184GrowingEulerMoments

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.C0184WeightedSource

noncomputable section

/-- The explicit C-0180 Gaussian-Hermite baseline carrier. -/
def hProfile (x : ℝ) : ℝ :=
  x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)

/-- The formal C-0180 superheat operator `exp (-alpha * mathcalZ^k)`,
using the canonical shifted-Euler carrier. -/
def superheatOperator (α : ℝ) (k : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∑' n : ℕ,
    ((-α) ^ n / (Nat.factorial n : ℝ)) *
      ((C0184.mathcalZ^[k * n]) f) x

def baselineCarrier (α : ℝ) (k : ℕ) : ℝ → ℝ :=
  superheatOperator α k hProfile

/-- The fixed source seminorm represented by the C-0180 `L¹` source size and
its second ordinary derivative. -/
noncomputable def sourceSeminorm (f : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, |f x|) +
    (∫ x : ℝ, |deriv (deriv f) x|)

/-- Claim 2734: the weighted C-0180 source-seminorm estimate, with the
shifted-Euler carriers fixed rather than supplied as callbacks. -/
def weightedSourceSeminormEstimate_claim2734
    (k : ℕ) (α : ℝ) : Prop :=
  1 ≤ k ∧ 0 < α ∧
    ∀ m : ℕ, ∃ C_m : ℝ, 0 < C_m ∧
      ∀ j : ℕ,
        sourceSeminorm
            ((C0184.mathcalL^[m]) ((C0184.mathcalZ^[j]) (baselineCarrier α k))) ≤
          Real.rpow (C_m * (j + 1 : ℝ))
            ((j : ℝ) / (k : ℝ) + C_m)

end

end MathlibPlus.Open.ResearchFormalization.C0184WeightedSource
