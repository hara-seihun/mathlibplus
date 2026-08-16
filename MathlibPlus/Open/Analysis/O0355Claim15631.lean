import Mathlib

open scoped BigOperators Topology
open Filter Asymptotics

namespace MathlibPlus.Open.Analysis.O0355Claim15631

noncomputable section

private noncomputable def counterfeitPsi
    (aY : ℕ → ℕ → ℝ) (Y : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (Nat.floor x + 1)).sum (fun p =>
    (Finset.range (Nat.floor x + 1)).sum (fun k =>
      if Nat.Prime p ∧ 1 ≤ k ∧ ((p ^ k : ℕ) : ℝ) ≤ x then
        (aY Y p) ^ k * Real.log (p : ℝ)
      else 0))

private noncomputable def vkRate (c x : ℝ) : ℝ :=
  x * Real.exp
    (-c * Real.rpow (Real.log x) (3 / 5 : ℝ) *
      Real.rpow (Real.log (Real.log x)) (-1 / 5 : ℝ))

private def zetaVinogradovKorobov : Prop :=
  ∃ c : ℝ, 0 < c ∧
    IsBigO atTop
      (fun x : ℝ => |Chebyshev.psi x - x|)
      (fun x : ℝ => vkRate c x)

private def counterfeitPowerDiscrepancyBound
    (aY : ℕ → ℕ → ℝ) (alpha : ℝ) : Prop :=
  ∀ᶠ Y : ℕ in atTop,
    IsBigO atTop
      (fun x : ℝ => |counterfeitPsi aY Y x - Chebyshev.psi x|)
      (fun x : ℝ => Real.rpow x (1 - alpha))

/-- Claim 15631: the actual generalized prime-power counting function
inherits the zeta Vinogradov--Korobov error once its actual power discrepancy
has the admitted `x^(1-alpha)` bound. -/
def claim15631 : Prop :=
  ∀ (alpha : ℝ) (aY : ℕ → ℕ → ℝ),
    0 < alpha →
      counterfeitPowerDiscrepancyBound aY alpha →
        zetaVinogradovKorobov →
          ∃ c : ℝ, 0 < c ∧
            ∀ᶠ Y : ℕ in atTop,
              IsBigO atTop
                (fun x : ℝ =>
                  |counterfeitPsi aY Y x - x|)
                (fun x : ℝ => vkRate c x)

end

end MathlibPlus.Open.Analysis.O0355Claim15631
