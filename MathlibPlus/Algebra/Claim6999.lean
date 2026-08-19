import Mathlib

namespace MathlibPlus.Algebra.Claim6999

noncomputable section

/-- The displayed raised Schur contribution. -/
def raisedSchurBranch (s : ℂ) : ℂ :=
  (1 - s) / 4

/-- The displayed lowering-return contribution. -/
def loweringReturn (k : ℕ) : ℂ :=
  -(k : ℂ) / 4

/-- The exact recombined Schur--Hodge reserve, with the source relation
`α = s + k - 1` retained and `k` kept as the natural lowest-weight index. -/
def recombinedSchurHodgeReserve : Prop :=
  ∀ (s : ℂ) (k : ℕ) (α : ℂ),
    α = s + (k : ℂ) - 1 →
      raisedSchurBranch s + loweringReturn k = -α / 4 ∧
        (1 - s) / 4 - (k : ℂ) / 4 = -α / 4

end

end MathlibPlus.Algebra.Claim6999
