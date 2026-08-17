import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchO0078

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0078.Claim12115

noncomputable section

/-- The carrier quotient `ξ(s)/C_m(s)` from the shifted-gamma construction. -/
noncomputable def shiftedH (m : ℕ) (s : ℂ) : ℂ :=
  xi s / gammaCarrier m s

/-- The elementary quotient written with the Riemann-zeta carrier. -/
noncomputable def elementaryH (m : ℕ) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (m - 1) * (s - 1) * riemannZeta s /
    Finset.prod (Finset.Icc (1 : ℕ) (m - 1)) (fun j => s + 2 * (j : ℂ))

def claim12115 : Prop :=
  (∀ (m : ℕ), 1 ≤ m → ∀ s : ℂ,
    shiftedH m s = elementaryH m s) ∧
  (∀ s : ℂ,
    shiftedH 6 s =
      32 * (s - 1) * riemannZeta s /
        ((s + 2) * (s + 4) * (s + 6) * (s + 8) * (s + 10)))

end

end MathlibPlus.Open.ResearchFormalization.BatchO0078.Claim12115
