import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace MathlibPlus.Analysis.Claim53408

/-- The algebraic core of the full-parity transcript inequality in admitted claim
53408.  The source names `n`, `t`, `Q`, `R`, and `Ψ` but defines them in the
R-4093 transcript setup; this theorem records the displayed identities and the
stated consequences once those quantities have their indicated real meanings.
-/
theorem sharpTranscriptInequality
    (n : ℕ) (t Q R Ψ : ℝ)
    (ht_lower : -1 ≤ t) (ht_upper : t ≤ 1)
    (hR : R = (1 - t ^ 2) * Q)
    (hΨ : Ψ = t ^ 2 * ((n : ℝ) - Q))
    (hQ : (n : ℝ) * t ^ 2 ≤ Q) :
    R - Ψ = Q - (n : ℝ) * t ^ 2 ∧
      0 ≤ R - Ψ ∧
      Ψ ≤ R ∧
      (Ψ = R → Q = (n : ℝ) * t ^ 2) ∧
      Ψ ≤ 2 * R := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have ht_sq : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
  have hQ_nonneg : 0 ≤ Q := by nlinarith [sq_nonneg t]
  have hR_nonneg : 0 ≤ R := by rw [hR]; positivity
  have hdiff : R - Ψ = Q - (n : ℝ) * t ^ 2 := by
    rw [hR, hΨ]
    ring
  refine ⟨hdiff, ?_, ?_, ?_, ?_⟩
  · rw [hdiff]
    linarith
  · linarith [hdiff]
  · intro hEq
    linarith [hdiff]
  · linarith

end MathlibPlus.Analysis.Claim53408
