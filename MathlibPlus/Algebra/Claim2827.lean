import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim2827

open PowerSeries

/-- The exact formal-power-series core of claim 2827's deflated cyclic shell.
After removing the positive factor, the residual shell is `1 + z^2`; its
reciprocal has alternating even coefficients and zero odd coefficients. -/
theorem cyclicShellDeflation_claim2827 :
    ∀ n : ℕ,
      PowerSeries.coeff n ((1 + X ^ 2 : PowerSeries ℝ)⁻¹) =
        if Even n then (-1 : ℝ) ^ (n / 2) else 0 := by
  intro n
  let H : PowerSeries ℝ := (1 + X ^ 2 : PowerSeries ℝ)⁻¹
  have hprod : (1 + X ^ 2 : PowerSeries ℝ) * H = 1 := by
    dsimp [H]
    apply PowerSeries.mul_inv_cancel
    norm_num
  have hprod' : (1 : PowerSeries ℝ) * H + X ^ 2 * H = 1 := by
    calc
      (1 : PowerSeries ℝ) * H + X ^ 2 * H = (1 + X ^ 2) * H := by ring
      _ = 1 := hprod
  have hrec (k : ℕ) :
      PowerSeries.coeff k H +
          (if 2 ≤ k then PowerSeries.coeff (k - 2) H else 0) =
        (if k = 0 then 1 else 0) := by
    have hk := congrArg (PowerSeries.coeff k) hprod'
    simpa [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one, PowerSeries.coeff_mk] using hk
  have hformula : ∀ k : ℕ,
      PowerSeries.coeff k H = if Even k then (-1 : ℝ) ^ (k / 2) else 0 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        have h0 := hrec 0
        norm_num at h0 ⊢
        exact h0
    | one =>
        have h1 := hrec 1
        norm_num at h1 ⊢
        exact h1
    | more k hk0 hk1 =>
        have hr := hrec (k + 2)
        have hparity : Even (k + 2) ↔ Even k := by
          rw [Nat.even_iff, Nat.even_iff]
          omega
        have hshift : (k + 2) / 2 = k / 2 + 1 := by omega
        have hnext :
            (if Even (k + 2) then (-1 : ℝ) ^ ((k + 2) / 2) else 0) =
              -(if Even k then (-1 : ℝ) ^ (k / 2) else 0) := by
          by_cases he : Even k
          · rw [if_pos (hparity.mpr he), if_pos he, hshift, pow_succ]
            ring
          · have he' : ¬ Even (k + 2) := by
              intro h
              exact he (hparity.mp h)
            rw [if_neg he', if_neg he]
            norm_num
        rw [show (k + 2) - 2 = k by omega] at hr
        norm_num at hr
        rw [hk0] at hr
        rw [hnext]
        linarith
  simpa [H] using hformula n

end MathlibPlus.Algebra.Claim2827
