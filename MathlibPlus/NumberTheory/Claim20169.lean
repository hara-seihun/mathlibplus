import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim20169

/-- Every product of eight numbers in `(R / 2, R]` has logarithm in the
source's short interval; the last inequality is the rational width bound used
by the selected-prime argument. -/
theorem selectedEightLogInterval_claim20169
    {R : ℝ} (hR : 0 < R) :
    (∀ p : Fin 8 → ℝ,
      (∀ i, R / 2 < p i ∧ p i ≤ R) →
        8 * Real.log (R / 2) < Real.log (∏ i, p i) ∧
        Real.log (∏ i, p i) ≤ 8 * Real.log R) ∧
      8 * Real.log R - 8 * Real.log (R / 2) = 8 * Real.log 2 ∧
      8 * Real.log 2 < 28 / 5 := by
  have hhalf : 0 < R / 2 := by positivity
  have hlog2 : Real.log (2 : ℝ) < (7 / 10 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  constructor
  · intro p hp
    have hprod_pos : 0 < ∏ i, p i :=
      Finset.prod_pos (fun i hi => hhalf.trans (hp i).1)
    have hprod_lower : (R / 2) ^ 8 < ∏ i, p i := by
      have h := Finset.prod_lt_prod
        (s := (Finset.univ : Finset (Fin 8)))
        (fun i hi => hhalf)
        (fun i hi => (hp i).1.le)
        ⟨0, Finset.mem_univ _, (hp 0).1⟩
      simpa [Finset.prod_const, Finset.card_univ, div_pow] using h
    have hprod_upper : (∏ i, p i) ≤ R ^ 8 := by
      have h := Finset.prod_le_prod
        (s := (Finset.univ : Finset (Fin 8)))
        (fun i hi => (le_of_lt (hhalf.trans (hp i).1)))
        (fun i hi => (hp i).2)
      simpa [Finset.prod_const, Finset.card_univ] using h
    have hlog_lower : Real.log ((R / 2) ^ 8) < Real.log (∏ i, p i) :=
      Real.strictMonoOn_log
        (show (R / 2) ^ 8 ∈ Set.Ioi (0 : ℝ) by
          change 0 < (R / 2) ^ 8
          positivity)
        (show (∏ i, p i) ∈ Set.Ioi (0 : ℝ) from hprod_pos)
        hprod_lower
    have hlog_upper : Real.log (∏ i, p i) ≤ Real.log (R ^ 8) :=
      Real.strictMonoOn_log.monotoneOn
        (show (∏ i, p i) ∈ Set.Ioi (0 : ℝ) from hprod_pos)
        (show R ^ 8 ∈ Set.Ioi (0 : ℝ) by
          change 0 < R ^ 8
          positivity)
        hprod_upper
    rw [Real.log_pow] at hlog_lower hlog_upper
    constructor <;> simpa using ‹_›
  constructor
  · rw [Real.log_div (ne_of_gt hR) (by norm_num)]
    ring
  · nlinarith

end MathlibPlus.NumberTheory.Claim20169
