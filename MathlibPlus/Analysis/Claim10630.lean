import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Analysis.Claim10630

local notation "P(" x "," p ")" => Polynomial.eval x (ascPochhammer ℝ p)

lemma p_succ (x : ℝ) (p : ℕ) : P(x,p+1) = P(x,p) * (x + (p : ℝ)) := by
  exact ascPochhammer_succ_eval p x

lemma p_succ_pred (x : ℝ) {p : ℕ} (hp : 0 < p) :
    P(x,p) = P(x,p-1) * (x + ((p - 1 : ℕ) : ℝ)) := by
  have h := p_succ x (p - 1)
  have hple : 1 ≤ p := by omega
  rw [Nat.sub_add_cancel hple] at h
  exact h

lemma p_shift_mul (x : ℝ) : ∀ p : ℕ, 0 < p →
    P(x,p) = x * P(x+1,p-1) := by
  intro p
  induction p with
  | zero => intro hp; omega
  | succ p ih =>
      intro hp
      by_cases hp0 : p = 0
      · subst p
        simp [ascPochhammer_zero, ascPochhammer_one]
      · have hppos : 0 < p := Nat.pos_of_ne_zero hp0
        have hi := ih hppos
        rw [p_succ]
        simp only [Nat.add_sub_cancel]
        rw [hi]
        have hrec := p_succ_pred (x + 1) hppos
        rw [hrec]
        have hnat : p = 1 + (p - 1) := by omega
        have hcast : ((p : ℕ) : ℝ) = 1 + ((p - 1 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        rw [hcast]
        ring

lemma p_diff (x : ℝ) (p : ℕ) :
    P(x+1,p) - P(x,p) = (p : ℝ) * P(x+1,p-1) := by
  cases p with
  | zero => simp [ascPochhammer_zero]
  | succ n =>
      by_cases hn : n = 0
      · subst n
        simp [ascPochhammer_zero, ascPochhammer_one]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hshift := p_shift_mul x n hnpos
        have hrec := p_succ_pred (x + 1) hnpos
        simp only [Nat.succ_sub_one]
        rw [p_succ, p_succ, hshift, hrec]
        have hnat : n = 1 + (n - 1) := by omega
        have hcast : ((n : ℕ) : ℝ) = 1 + ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        rw [hcast]
        norm_num [Nat.cast_add, Nat.cast_one]
        rw [hcast]
        ring

/-- The ordinary nonnegative gamma assembly, with Mathlib's canonical
ascending Pochhammer polynomial, is concentrated at index zero. -/
theorem ordinaryNonnegativeGammaAssemblyTrivial
    (α : ℝ) (w : ℕ → ℝ)
    (hα : 0 < α)
    (hw : ∀ p, 0 ≤ w p)
    (h0 : Summable (fun p => w p * P(α,p)))
    (h1 : Summable (fun p => w p * P(α+1,p)))
    (hnorm : ∀ q : ℕ,
      ∑' p, w p * P(α + (q : ℝ),p) = 1) :
    w 0 = 1 ∧ ∀ p, 0 < p → w p = 0 := by
  have hnorm0 : ∑' p, w p * P(α,p) = 1 := by
    simpa using hnorm 0
  have hnorm1 : ∑' p, w p * P(α+1,p) = 1 := by
    simpa using hnorm 1
  have hdiff : Summable (fun p => w p * (P(α+1,p) - P(α,p))) := by
    simpa [mul_sub] using h1.sub h0
  have hzero : ∑' p, w p * (P(α+1,p) - P(α,p)) = 0 := by
    calc
      (∑' p, w p * (P(α+1,p) - P(α,p))) =
          (∑' p, w p * P(α+1,p)) - (∑' p, w p * P(α,p)) := by
            simpa [mul_sub] using h1.tsum_sub h0
      _ = 0 := by rw [hnorm1, hnorm0]; norm_num
  have hdelta_nonneg : ∀ p,
      0 ≤ w p * (P(α+1,p) - P(α,p)) := by
    intro p
    by_cases hp : p = 0
    · subst p
      simp [ascPochhammer_zero]
    · have hppos : 0 < p := Nat.pos_of_ne_zero hp
      have hprod : P(α,p) < P(α+1,p) := by
        apply sub_pos.mp
        rw [p_diff]
        have hpos : 0 < P(α+1,p-1) := ascPochhammer_pos _ _ (by linarith)
        positivity
      exact mul_nonneg (hw p) (sub_nonneg.mpr hprod.le)
  have hterm_zero : ∀ p,
      w p * (P(α+1,p) - P(α,p)) = 0 := by
    intro p
    have hnonpos : w p * (P(α+1,p) - P(α,p)) ≤ 0 := by
      by_contra hpos
      have hpos' : 0 < w p * (P(α+1,p) - P(α,p)) := lt_of_not_ge hpos
      have htsumpos := hdiff.tsum_pos hdelta_nonneg p hpos'
      linarith [hzero]
    exact le_antisymm hnonpos (hdelta_nonneg p)
  have hwp : ∀ p, 0 < p → w p = 0 := by
    intro p hp
    have hprod : P(α,p) < P(α+1,p) := by
      apply sub_pos.mp
      rw [p_diff]
      have hpos : 0 < P(α+1,p-1) := ascPochhammer_pos _ _ (by linarith)
      positivity
    have hdelta : P(α+1,p) - P(α,p) ≠ 0 := ne_of_gt (sub_pos.mpr hprod)
    rcases mul_eq_zero.mp (hterm_zero p) with hwzero | hdzero
    · exact hwzero
    · exact False.elim (hdelta hdzero)
  have htail : ∑' p, w (p + 1) * P(α,p+1) = 0 := by
    calc
      (∑' p, w (p + 1) * P(α,p+1)) = ∑' _ : ℕ, 0 := by
        apply tsum_congr
        intro p
        rw [hwp (p + 1) (by omega), zero_mul]
      _ = 0 := tsum_zero
  have hsplit := h0.tsum_eq_zero_add
  rw [hnorm0, htail] at hsplit
  constructor
  · simpa [ascPochhammer_zero] using hsplit.symm
  · exact hwp

end MathlibPlus.Analysis.Claim10630
