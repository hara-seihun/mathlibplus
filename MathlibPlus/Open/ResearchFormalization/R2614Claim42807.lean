import MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

namespace MathlibPlus.Open.ResearchFormalization.R2614Claim42807

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

def kernelSupported (R : ℕ) (q s : ℤ) : Prop :=
  0 ≤ (R : ℤ) + s - 1 ∧
    s ≤ q ∧ q ≤ (R : ℤ) + 2 * s

/-- An index for which both the slack-`R` kernel and its slack-`R-1`
predecessor have the displayed nonnegative exponent. -/
def recurrenceSupported (R : ℕ) (q s : ℤ) : Prop :=
  1 ≤ R ∧
    0 ≤ (R : ℤ) + s - 2 ∧
      s ≤ q ∧ q ≤ (R : ℤ) + 2 * s

/-- Claim 42807: Pascal recurrence for the Laurent coefficient kernel on
all of its supported integer-offset indices. -/
def claim42807 : Prop :=
  ∀ (R : ℕ) (q s : ℤ),
    recurrenceSupported R q s →
      rowUniformLaurentKernel R q s =
        rowUniformLaurentKernel (R - 1) q s +
          rowUniformLaurentKernel (R - 1) (q - 1) s



end

end MathlibPlus.Open.ResearchFormalization.R2614Claim42807
