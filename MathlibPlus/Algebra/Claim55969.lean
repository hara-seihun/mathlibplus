import Mathlib

namespace MathlibPlus.Algebra.Claim55969

open scoped BigOperators

noncomputable section

variable (p : ℕ) [Fact p.Prime]

private abbrev K (p : ℕ) := ZMod p

def coefficient (i j : K p) : K p :=
  (if j = i + 1 then -i else 0) +
    (if i = 0 ∧ j = 1 then (2 : K p)⁻¹ else 0) +
    (if i = 1 ∧ j = 0 then (2 : K p)⁻¹ else 0)

def rowSum (i : K p) : K p := ∑ j : K p, coefficient p i j

def columnSum (j : K p) : K p := ∑ i : K p, coefficient p i j

private lemma sum_base_row (i : K p) :
    (∑ j : K p, if j = i + 1 then -i else 0) = -i := by
  exact Fintype.sum_ite_eq' (i + 1) (fun _ : K p => -i)

private lemma sum_correction_row (i : K p) :
    (∑ j : K p, if i = 0 ∧ j = 1 then (2 : K p)⁻¹ else 0) =
      if i = 0 then (2 : K p)⁻¹ else 0 := by
  by_cases hi : i = 0
  · subst i
    simp
  · simp [hi]

private lemma sum_correction_row' (i : K p) :
    (∑ j : K p, if i = 1 ∧ j = 0 then (2 : K p)⁻¹ else 0) =
      if i = 1 then (2 : K p)⁻¹ else 0 := by
  by_cases hi : i = 1
  · subst i
    simp
  · simp [hi]

private lemma rowSum_formula (i : K p) :
    rowSum p i = -i + (if i = 0 then (2 : K p)⁻¹ else 0) +
      (if i = 1 then (2 : K p)⁻¹ else 0) := by
  simp only [rowSum, coefficient, Finset.sum_add_distrib, sum_base_row,
    sum_correction_row, sum_correction_row']

private lemma sum_base_col (j : K p) :
    (∑ i : K p, if j = i + 1 then -i else 0) = -(j - 1) := by
  -- the unique contributing row is `j - 1`.
  have hfun : (fun i : K p => if j = i + 1 then -i else 0) =
      (fun i => if i = j - 1 then -i else 0) := by
    funext i
    have hcond : (j = i + 1) ↔ (i = j - 1) := by
      constructor
      · intro h
        rw [h]
        simp
      · intro h
        rw [h]
        simp
    simp only [hcond]
  rw [hfun]
  simp

private lemma sum_correction_col (j : K p) :
    (∑ i : K p, if i = 0 ∧ j = 1 then (2 : K p)⁻¹ else 0) =
      if j = 1 then (2 : K p)⁻¹ else 0 := by
  by_cases hj : j = 1
  · subst j
    simp
  · simp [hj]

private lemma sum_correction_col' (j : K p) :
    (∑ i : K p, if i = 1 ∧ j = 0 then (2 : K p)⁻¹ else 0) =
      if j = 0 then (2 : K p)⁻¹ else 0 := by
  by_cases hj : j = 0
  · subst j
    simp
  · simp [hj]

private lemma columnSum_formula (j : K p) :
    columnSum p j = -(j - 1) + (if j = 1 then (2 : K p)⁻¹ else 0) +
      (if j = 0 then (2 : K p)⁻¹ else 0) := by
  simp only [columnSum, coefficient, Finset.sum_add_distrib, sum_base_col,
    sum_correction_col, sum_correction_col']

private lemma row_col_sub (i : K p) : rowSum p i - columnSum p i = -1 := by
  rw [rowSum_formula, columnSum_formula]
  ring

private lemma coefficient_diag (i : K p) : coefficient p i i = 0 := by
  by_cases h0 : i = 0
  · subst i
    simp [coefficient]
  by_cases h1 : i = 1
  · subst i
    simp [coefficient]
  simp [coefficient, h0, h1]

private lemma two_ne_zero_of_odd (hpodd : Odd p) : (2 : K p) ≠ 0 := by
  intro h
  have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (K p) p 2).mp h
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p)
    Nat.prime_two).mp hdiv
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  rcases hpodd with ⟨k, hk⟩
  rw [two_mul] at hk
  omega

private lemma sum_zmod_eq_zero (hpodd : Odd p) : (∑ i : K p, i) = 0 := by
  have hp3 : 3 ≤ p := by
    have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    rcases hpodd with ⟨k, hk⟩
    rw [two_mul] at hk
    omega
  have hcard : 1 < Fintype.card (K p) - 1 := by
    rw [ZMod.card]
    omega
  simpa using (FiniteField.sum_pow_lt_card_sub_one (K p) 1 hcard)

private lemma sum_rowSum_eq_one (hpodd : Odd p) : (∑ i : K p, rowSum p i) = 1 := by
  rw [Finset.sum_congr rfl (fun i _ => rowSum_formula p i)]
  simp_rw [Finset.sum_add_distrib]
  have hneg : (∑ i : K p, -i) = -(∑ i : K p, i) := by
    simpa using (Finset.sum_neg_distrib (s := Finset.univ) (fun i : K p => i))
  rw [hneg, sum_zmod_eq_zero p hpodd]
  simp only [neg_zero, zero_add]
  rw [Fintype.sum_ite_eq' (0 : K p), Fintype.sum_ite_eq' (1 : K p)]
  have h2 := two_ne_zero_of_odd p hpodd
  rw [← two_mul, mul_inv_cancel₀ h2]

end
theorem matrixIdentities_claim55969 (p : ℕ) [Fact p.Prime] (hpodd : Odd p) :
    (∀ i : ZMod p, coefficient p i i = 0) ∧
      (∀ i : ZMod p, rowSum p i - columnSum p i = -1) ∧
      (∑ i : ZMod p, rowSum p i) = 1 := by
  refine ⟨fun i => coefficient_diag p i, fun i => row_col_sub p i,
    sum_rowSum_eq_one p hpodd⟩

end MathlibPlus.Algebra.Claim55969
