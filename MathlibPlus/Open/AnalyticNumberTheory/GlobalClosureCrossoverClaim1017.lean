import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- The classical amplitude region used by Claim 1017. -/
def classicalRegionClaim1017 (A H : ℝ) : Prop :=
  ∀ (t σ : ℝ),
    H ≤ t →
      σ > 1 - A / Real.log t →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- The finite-height part supplied by one variable-width iteration step. -/
def classicalRegionUpToClaim1017 (A H T : ℝ) : Prop :=
  ∀ (t σ : ℝ),
    H ≤ t →
      t ≤ T →
        σ > 1 - A / Real.log t →
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- The large-height Littlewood region from Claim 1012. -/
def littlewoodRegionClaim1017 : Prop :=
  ∀ (t σ : ℝ),
    3 ≤ t →
      σ > 1 - Real.log (Real.log t) / ((19.62 : ℝ) * Real.log t) →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Claim 1017: the exact Littlewood crossover contains every intermediate
classical amplitude through `A₀ = 1 / 4.8594`, and its overlap with the
finite iteration range restores a global classical hypothesis. -/
def globalClosureCrossover_claim1017 : Prop :=
  let A₀ : ℝ := 1 / 4.8594
  let H : ℝ := 3 * 10 ^ 12
  let T : ℝ := Real.exp 56.693
  (∀ A' : ℝ, A' ≤ A₀ →
    ∀ t : ℝ,
      3 ≤ t →
        Real.exp ((19.62 : ℝ) * A') ≤ Real.log t →
          ∀ σ : ℝ,
            σ > 1 - A' / Real.log t →
              σ > 1 - Real.log (Real.log t) /
                ((19.62 : ℝ) * Real.log t)) ∧
    ((56686466615244797557 : ℝ) / 10 ^ (18 : ℕ)) <
      Real.exp ((19.62 : ℝ) / 4.8594) ∧
    Real.exp ((19.62 : ℝ) / 4.8594) < 56.693 ∧
    (∀ A' : ℝ, A' ≤ A₀ →
      Real.exp ((19.62 : ℝ) * A') ≤
        Real.exp ((19.62 : ℝ) / 4.8594)) ∧
    (littlewoodRegionClaim1017 →
      ∀ A' : ℝ, A' ≤ A₀ →
        classicalRegionUpToClaim1017 A' H T →
          classicalRegionClaim1017 A' H)

end MathlibPlus.Open.AnalyticNumberTheory
