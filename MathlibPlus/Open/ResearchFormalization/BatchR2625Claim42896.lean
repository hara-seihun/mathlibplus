import MathlibPlus.Algebra.Claim42889
import MathlibPlus.Open.ResearchFormalizationBatch.Shell

namespace MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42896

open scoped BigOperators
open MathlibPlus.Algebra.Claim42889
open MathlibPlus.Open.ResearchFormalizationBatch.Shell

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Vec4 := Fin 4 → ℝ

def shellVector (n : ℕ) : Vec4 :=
  fun k => dividedShellMoment n k.val

def divisibleShellSummand (d : ℕ) (k : Fin 4) (n : ℕ) : ℝ :=
  if 1 ≤ n ∧ d ∣ n then shellVector n k else 0

def divisibleShellVector (d : ℕ) : Vec4 :=
  fun k => ∑' n : ℕ, divisibleShellSummand d k n

def determinantTailMajorant (r : ℕ) : ℝ :=
  Real.exp (-4 * Real.pi * (r : ℝ) ^ 2) /
    (Real.pi * (r : ℝ) ^ 2)

/-- The componentwise divisible even-shell bound and the strict determinant
bound from the explicit quadratic, cubic, and quartic coefficient sums. -/
def divisibleEvenShellDeterminantTail_claim42896 : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    (∀ k : Fin 4,
      divisibleShellVector (2 * r) k ≤ determinantTailMajorant r) ∧
    |determinantPieces (divisibleShellVector (2 * r))| <
      3 * (determinantTailMajorant r) ^ 2

end
end MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42896
