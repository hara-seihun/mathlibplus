import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory

private lemma weighted_sum_Icc_two (x : ℚ) (m : ℕ) (hm : 2 ≤ m) :
    (∑ d ∈ Finset.Icc 2 m,
      (x + (d : ℚ)) / (2 : ℚ) ^ d) =
      x / 2 + 3 / 2 - (x + (m : ℚ) + 2) / (2 : ℚ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num; ring
  | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      simp only [pow_succ]
      push_cast
      field_simp
      ring

private lemma balanced_identity_of_relation (H N : ℕ) (hH : 5 ≤ H)
    (hN : 3 * N + 3 * H + 2 = 2 ^ H) :
    (∑ i ∈ Finset.Icc 2 (H - 1),
      ((N + i : ℕ) : ℚ) / (2 : ℚ) ^ (N + i)) =
    ((N + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (N + 1) +
      ((N + H : ℕ) : ℚ) / (2 : ℚ) ^ (N + H) := by
  have hHm : 2 ≤ H - 1 := by omega
  have hsum := weighted_sum_Icc_two (N : ℚ) (H - 1) hHm
  have hscale :
      (∑ i ∈ Finset.Icc 2 (H - 1),
        ((N + i : ℕ) : ℚ) / (2 : ℚ) ^ (N + i)) =
      (1 / (2 : ℚ) ^ N) *
        (∑ i ∈ Finset.Icc 2 (H - 1),
          ((N : ℚ) + (i : ℚ)) / (2 : ℚ) ^ i) := by
    calc
      (∑ i ∈ Finset.Icc 2 (H - 1),
          ((N + i : ℕ) : ℚ) / (2 : ℚ) ^ (N + i)) =
          ∑ i ∈ Finset.Icc 2 (H - 1),
            (1 / (2 : ℚ) ^ N) * ((N : ℚ) + (i : ℚ)) / (2 : ℚ) ^ i := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Nat.cast_add, pow_add]
              field_simp
      _ = (1 / (2 : ℚ) ^ N) *
          (∑ i ∈ Finset.Icc 2 (H - 1),
            ((N : ℚ) + (i : ℚ)) / (2 : ℚ) ^ i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
  have hNq :
      (3 : ℚ) * N + 3 * H + 2 = (2 : ℚ) ^ H := by
    exact_mod_cast hN
  have hscaled :
      (N : ℚ) / 2 + 3 / 2 - ((N : ℚ) + H + 1) / (2 : ℚ) ^ (H - 1) =
        ((N : ℚ) + 1) / 2 + ((N : ℚ) + H) / (2 : ℚ) ^ H := by
    have hpows : (2 : ℚ) ^ (H - 1) * 2 = (2 : ℚ) ^ H := by
      rw [← pow_succ]
      congr 1
      omega
    rw [← hpows] at hNq ⊢
    field_simp
    ring_nf
    linear_combination -hNq
  rw [hscale, hsum]
  have hlast :
      (1 / (2 : ℚ) ^ N) *
          ((N : ℚ) / 2 + 3 / 2 -
            ((N : ℚ) + ((H - 1 : ℕ) : ℚ) + 2) / (2 : ℚ) ^ (H - 1)) =
        (1 / (2 : ℚ) ^ N) *
          (((N : ℚ) + 1) / 2 + ((N : ℚ) + H) / (2 : ℚ) ^ H) := by
    congr 1
    rw [Nat.cast_sub (by omega)]
    norm_num
    convert hscaled using 1 <;> ring
  rw [hlast]
  rw [show (2 : ℚ) ^ (N + 1) = (2 : ℚ) ^ N * 2 by rw [pow_add]; norm_num]
  rw [show (2 : ℚ) ^ (N + H) = (2 : ℚ) ^ N * (2 : ℚ) ^ H by rw [pow_add]]
  field_simp
  push_cast
  ring

private lemma pow_mod_three_of_odd {H : ℕ} (h : Odd H) : 2 ^ H % 3 = 2 := by
  rcases h with ⟨k, rfl⟩
  have hk : 4 ^ k % 3 = 1 := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ, Nat.mul_mod, ih]
  rw [pow_add, pow_mul]
  norm_num [Nat.pow_mod]
  rw [Nat.mul_mod, hk]

private lemma pow_ge_linear : ∀ H : ℕ, 5 ≤ H → 3 * H + 2 ≤ 2 ^ H := by
  intro H
  induction H with
  | zero => intro h; omega
  | succ H ih =>
      intro h
      by_cases h5 : 5 ≤ H
      · rw [pow_succ]
        have hi := ih h5
        nlinarith
      · have hH : H = 4 := by omega
        subst H
        norm_num

private lemma pow_ge_linear_plus_three : ∀ H : ℕ, 5 ≤ H → 3 * H + 5 ≤ 2 ^ H := by
  intro H
  induction H with
  | zero => intro h; omega
  | succ H ih =>
      intro h
      by_cases h5 : 5 ≤ H
      · rw [pow_succ]
        have hi := ih h5
        nlinarith
      · have hH : H = 4 := by omega
        subst H
        norm_num

private lemma defining_relation (H : ℕ) (hH : 5 ≤ H) (ho : Odd H) :
    3 * ((2 ^ H - 3 * H - 2) / 3) + 3 * H + 2 = 2 ^ H := by
  have hp : 2 ^ H % 3 = 2 := pow_mod_three_of_odd ho
  have hb : 3 * H + 2 ≤ 2 ^ H := pow_ge_linear H hH
  have hmod : 3 * H + 2 ≡ 2 ^ H [MOD 3] := by
    simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod] using hp.symm
  have hdiv : 3 ∣ 2 ^ H - (3 * H + 2) :=
    (Nat.modEq_iff_dvd' hb).mp hmod
  have hmul : 3 * ((2 ^ H - (3 * H + 2)) / 3) = 2 ^ H - (3 * H + 2) :=
    Nat.mul_div_cancel' hdiv
  omega

/-- Claim 51689: every odd `H ≥ 5` gives the exact endpoint/interior
weighted-binary representation.  The quotient definitions of `N` and `K`,
their parity, and the balanced identity are all retained literally. -/
theorem endpointInteriorBalancedIdentity_claim51689
    (H : ℕ) (hH : 5 ≤ H) (ho : Odd H) :
    let N := (2 ^ H - 3 * H - 2) / 3
    let K := N + H
    1 ≤ N ∧ Odd N ∧ Even K ∧ K = (2 ^ H - 2) / 3 ∧
      (∑ i ∈ Finset.Icc 2 (H - 1),
        ((N + i : ℕ) : ℚ) / (2 : ℚ) ^ (N + i)) =
      ((N + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (N + 1) +
        ((N + H : ℕ) : ℚ) / (2 : ℚ) ^ (N + H) := by
  dsimp
  let N : ℕ := (2 ^ H - 3 * H - 2) / 3
  let K : ℕ := N + H
  have hN : 3 * N + 3 * H + 2 = 2 ^ H := by
    exact defining_relation H hH ho
  have hNpos : 1 ≤ N := by
    have hstrong := pow_ge_linear_plus_three H hH
    omega
  have hNevenpow : Even (2 ^ H) := by
    refine ⟨2 ^ (H - 1), ?_⟩
    have hp : 2 ^ (H - 1) * 2 = 2 ^ H := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      2 ^ H = 2 ^ (H - 1) * 2 := hp.symm
      _ = 2 ^ (H - 1) + 2 ^ (H - 1) := by ring
  have hNodd : Odd N := by
    rcases Nat.even_or_odd N with hNe | hNo
    · exfalso
      rcases hNe with ⟨a, ha⟩
      rcases ho with ⟨b, hb⟩
      rcases hNevenpow with ⟨c, hc⟩
      omega
    · exact hNo
  have hKeven : Even K := by
    dsimp [K]
    exact hNodd.add_odd ho
  have hKrel : 3 * K + 2 = 2 ^ H := by
    dsimp [K]
    omega
  have hKdiv : 3 ∣ 2 ^ H - 2 := by
    refine ⟨K, ?_⟩
    omega
  have hKmul : 3 * ((2 ^ H - 2) / 3) = 2 ^ H - 2 :=
    Nat.mul_div_cancel' hKdiv
  have hKformula : K = (2 ^ H - 2) / 3 := by
    omega
  exact ⟨hNpos, hNodd, hKeven, hKformula,
    balanced_identity_of_relation H N hH hN⟩

end MathlibPlus.NumberTheory
