import Mathlib

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain.ThetaDiagnostic

noncomputable section

/-- Claim 8613: exact rational intervals retain the recorded decimal-prefix
    diagnostics at `M = 7`, and the certificate inequalities are asserted at
    every stored prefix `M = 2, ..., 7`. -/
def claim8613_finiteThetaPrefixDiagnosticValues
    (trailingQuarterTransfer trailingQuarterCertificate trailingQuarterRatio :
      ℕ → ℝ)
    (trailingTenTransfer trailingTenCertificate trailingTenRatio : ℕ → ℝ) : Prop :=
  ((33292981 : ℝ) / (10 : ℝ) ^ 8 ≤ trailingQuarterTransfer 7 ∧
      trailingQuarterTransfer 7 < (33292982 : ℝ) / (10 : ℝ) ^ 8) ∧
    ((56499541 : ℝ) / (10 : ℝ) ^ 8 ≤ trailingQuarterCertificate 7 ∧
      trailingQuarterCertificate 7 < (56499542 : ℝ) / (10 : ℝ) ^ 8) ∧
    ((11072112 : ℝ) / (10 : ℝ) ^ 7 ≤ trailingQuarterRatio 7 ∧
      trailingQuarterRatio 7 < (11072113 : ℝ) / (10 : ℝ) ^ 7) ∧
    ((12576829 : ℝ) / (10 : ℝ) ^ 8 ≤ trailingTenTransfer 7 ∧
      trailingTenTransfer 7 < (12576830 : ℝ) / (10 : ℝ) ^ 8) ∧
    ((24287477 : ℝ) / (10 : ℝ) ^ 8 ≤ trailingTenCertificate 7 ∧
      trailingTenCertificate 7 < (24287478 : ℝ) / (10 : ℝ) ^ 8) ∧
    ((10441781 : ℝ) / (10 : ℝ) ^ 7 ≤ trailingTenRatio 7 ∧
      trailingTenRatio 7 < (10441782 : ℝ) / (10 : ℝ) ^ 7) ∧
    (∀ M : ℕ, 2 ≤ M → M ≤ 7 →
      trailingQuarterTransfer M ≤ trailingQuarterCertificate M ∧
        1 ≤ trailingQuarterRatio M ∧
        trailingTenTransfer M ≤ trailingTenCertificate M ∧
        1 ≤ trailingTenRatio M)

end
end MathlibPlus.Open.NewResearch2.FormalizationDrain.ThetaDiagnostic
