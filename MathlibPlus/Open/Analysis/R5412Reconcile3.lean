import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The constant in the paired complex norm from claim 60577. -/
noncomputable def r5412_reconcile3_kappa (a : ℝ) : ℝ :=
  (1 - a) / (1 + a)

/-- The paired majorant from claim 60577. -/
noncomputable def r5412_reconcile3_norm (a : ℝ) (u v : ℂ) : ℝ :=
  max ‖u - v‖ (r5412_reconcile3_kappa a * ‖u + v‖)

/-- Claim 60577: the lower bound and its sharpness witness. -/
def r5412_reconcile3_pair_bound : Prop :=
  ∀ (a : ℝ), 0 ≤ a → a < 1 →
    (∀ (u v : ℂ),
      r5412_reconcile3_norm a u v ≥ (1 - a) * ‖u‖) ∧
    r5412_reconcile3_norm a (-1 : ℂ) (-a : ℂ) =
      (1 - a) * ‖(-1 : ℂ)‖

end MathlibPlus.Open.Analysis
