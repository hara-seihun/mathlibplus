import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
Statement-fidelity registry node for admitted claim 1027.  The displayed
ellipsized value at the handoff is represented by its half-open prefix
interval.  The source names the zero-density constants and their domain but
does not define a separate predicate for “admissible”; the exact constants
and the transferred domain are therefore retained directly.
-/

/-- Claim 1027: the zero-density parameter stays in the stated domain from the
handoff onward, with the displayed handoff value and monotonicity certificate.
The constants `c₁` and `c₂` are retained as exact terminating decimals. -/
def zeroDensityHandoffDomain : Prop :=
  let Rstar : ℝ := 4.86201
  let sigma₂ : ℝ → ℝ := fun L => 1 - 2 / Real.sqrt (Rstar * L)
  let c₁ : ℝ := 17.4194
  let c₂ : ℝ := 2.9089
  let closedDomain : Set ℝ := Set.Icc (0.9 : ℝ) 1
  let tailDomain : Set ℝ := Set.Ico (0.9 : ℝ) 1
  (∀ L : ℝ, 2008 ≤ L → sigma₂ L ∈ tailDomain) ∧
    (0.9797586153668728 ≤ sigma₂ 2008 ∧
      sigma₂ 2008 < 0.9797586153668729) ∧
    MonotoneOn sigma₂ (Set.Ici (2008 : ℝ)) ∧
    (∀ L : ℝ, 2008 ≤ L → sigma₂ L ∈ closedDomain) ∧
    c₁ = 17.4194 ∧ c₂ = 2.9089

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
