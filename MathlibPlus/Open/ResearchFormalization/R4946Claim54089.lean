import Mathlib
import MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

open MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R4946

private noncomputable def originRow
    (τ : ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  2 * (n : ℝ) ^ (2 * k) * Real.exp (τ * (n : ℝ) ^ 2)

private noncomputable def targetRow (n : ℤ) : ℝ :=
  -2 * Real.exp (targetTime * (n : ℝ) ^ 2) *
    Real.cosh ((n : ℝ) * targetHeight)

private noncomputable def originFamilyContribution
    (τ : ℝ) (k : ℕ) (v : ℤ →₀ ℝ) : ℝ :=
  Finset.sum v.support (fun n => v n * originRow τ k n)

private noncomputable def targetFamilyContribution (v : ℤ →₀ ℝ) : ℝ :=
  Finset.sum v.support (fun n => v n * targetRow n)

/-- R-4946 claim 54089: a finite observation list has a finitely supported
real family on odd integers at least five which annihilates every origin row
but has nonzero target-row sum. -/
def claim54089_finiteJetAnnihilatingPerturbation : Prop :=
  ∀ (m : ℕ) (τ : Fin m → ℝ) (k : Fin m → ℕ),
    ∃ v : ℤ →₀ ℝ,
      (∀ n : ℤ, n ∈ v.support → Odd n ∧ 5 ≤ n) ∧
      (∀ j : Fin m,
        originFamilyContribution (τ j) (k j) v = 0) ∧
      targetFamilyContribution v ≠ 0

end MathlibPlus.Open.ResearchFormalization.R4946
