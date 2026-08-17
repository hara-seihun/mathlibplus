import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0117

noncomputable section

private def greenNumerator (n : ℕ+) (s : ℂ) : ℂ :=
  ((n : ℂ) + s) * (((n : ℕ) + 1 : ℕ) : ℂ) ^ (-s) -
    (n : ℂ) ^ (1 - s)

private def holomorphicCellExtension (n : ℕ+) (I : ℂ → ℂ) : Prop :=
  Differentiable ℂ I ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      I s = greenNumerator n s / (s * (1 - s)))

/-- Claim 18063: the exact Green cancellation identity holds for the
holomorphic, pole-free extension of each positive unit-cell quotient. -/
noncomputable def exactGreenCancellationIdentity_18063 : Prop :=
  ∀ n : ℕ+, ∃ I : ℂ → ℂ,
    holomorphicCellExtension n I ∧
      (∀ s : ℂ,
        s * (1 - s) * I s = greenNumerator n s)

end

end MathlibPlus.Open.ResearchFormalization.R0117
