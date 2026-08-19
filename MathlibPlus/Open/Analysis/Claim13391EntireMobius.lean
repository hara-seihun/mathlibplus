import Mathlib

open scoped BigOperators Filter Topology
open Filter
noncomputable section

namespace MathlibPlus.Open.Analysis.Claim13391EntireMobius

noncomputable def mobiusTerm (n : ℕ) (x : ℂ) : ℂ :=
  if 0 < n then
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (Complex.exp (-x / (n : ℂ)) - 1 + x / (n : ℂ))
  else 0

noncomputable def mobiusSeries (x : ℂ) : ℂ :=
  ∑' n : ℕ, mobiusTerm n x

def locallyUniformlyAbsolutelySummable
    (term : ℕ → ℂ → ℂ) (sum : ℂ → ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K →
    TendstoUniformlyOn
        (fun N z => ∑ n ∈ Finset.range N, ‖term n z‖)
        (fun z => ∑' n : ℕ, ‖term n z‖) atTop K ∧
      TendstoUniformlyOn
        (fun N z => ∑ n ∈ Finset.range N, term n z)
        sum atTop K

/-- Claim 13391: the all-prime Mobius series is absolutely and locally
uniformly convergent on the complex plane and its sum is entire. -/
def claim13391_entireAllPrimeMobiusLimit : Prop :=
  locallyUniformlyAbsolutelySummable mobiusTerm mobiusSeries ∧
    Differentiable ℂ mobiusSeries

end MathlibPlus.Open.Analysis.Claim13391EntireMobius
