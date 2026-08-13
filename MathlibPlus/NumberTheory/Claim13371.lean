import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim13371

noncomputable def quotientWeight (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹ ^ 2)

def quotientBlock (N d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun q => N / q = d)

noncomputable def quotientBlockWeight (N d : ℕ) : ℝ :=
  ∑ q ∈ quotientBlock N d, quotientWeight q

theorem quotientWeight_pos {q : ℕ} (hq : 1 ≤ q) : 0 < quotientWeight q := by
  classical
  unfold quotientWeight
  apply Finset.prod_pos
  intro p hp
  have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hprime.two_le
  have hp_inv_sq : (p : ℝ)⁻¹ ^ 2 < 1 := by
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have hpinv_nonneg : 0 ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  exact sub_pos.mpr hp_inv_sq

theorem quotientWeight_nonneg {q : ℕ} (hq : 1 ≤ q) : 0 ≤ quotientWeight q :=
  (quotientWeight_pos hq).le

theorem quotientBlockWeight_nonneg (N d : ℕ) :
    0 ≤ quotientBlockWeight N d := by
  classical
  unfold quotientBlockWeight
  apply Finset.sum_nonneg
  intro q hq
  have hq_one : 1 ≤ q := by
    exact (Finset.mem_Icc.mp ((Finset.mem_filter.1 hq).1)).1
  exact quotientWeight_nonneg hq_one

theorem quotientBlockWeight_pos_iff (N d : ℕ) :
    0 < quotientBlockWeight N d ↔ (quotientBlock N d).Nonempty := by
  classical
  unfold quotientBlockWeight
  have hnonneg : ∀ q ∈ quotientBlock N d, 0 ≤ quotientWeight q := by
    intro q hq
    have hq_one : 1 ≤ q := by
      exact (Finset.mem_Icc.mp ((Finset.mem_filter.1 hq).1)).1
    exact quotientWeight_nonneg hq_one
  constructor
  · intro hpos
    rw [Finset.sum_pos_iff_of_nonneg hnonneg] at hpos
    rcases hpos with ⟨q, hq, _⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, hq⟩
    apply Finset.sum_pos' hnonneg
    have hq_one : 1 ≤ q := by
      exact (Finset.mem_Icc.mp ((Finset.mem_filter.1 hq).1)).1
    exact ⟨q, hq, quotientWeight_pos hq_one⟩

end MathlibPlus.NumberTheory.Claim13371
