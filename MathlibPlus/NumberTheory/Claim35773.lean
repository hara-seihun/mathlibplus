import Mathlib

namespace MathlibPlus.NumberTheory.Claim35773

/-!
Claim 35773: exact weighted binary expansion for a period-`p` integer word.
The word is represented by `c : ℕ → ℤ`; only its one-based entries in
`Finset.Icc 1 p` occur in the statement, so values outside the word are
irrelevant. The positive-period hypothesis is explicit because the closed
form has denominator `2^p - 1`.
-/

open scoped BigOperators

private lemma weighted_geometric_hasSum' (p r : ℕ) (hp : 0 < p) :
    HasSum (fun k : ℕ =>
      (((r : ℝ) + (k * p : ℕ)) : ℝ) / (2 : ℝ) ^ (r + k * p))
      ((r : ℝ) / (2 : ℝ) ^ r / (1 - ((1 / 2 : ℝ) ^ p)) +
        (p : ℝ) / (2 : ℝ) ^ r * ((1 / 2 : ℝ) ^ p) /
          (1 - ((1 / 2 : ℝ) ^ p)) ^ 2) := by
  let q : ℝ := (1 / 2 : ℝ) ^ p
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact pow_lt_one₀ (by norm_num) (by norm_num) hp.ne'
  have hg : HasSum (fun k : ℕ => q ^ k) ((1 - q)⁻¹) :=
    hasSum_geometric_of_lt_one hq0 hq1
  have hn : HasSum (fun k : ℕ => (k : ℝ) * q ^ k) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  have hr : HasSum (fun k : ℕ => (r : ℝ) * q ^ k) ((r : ℝ) * (1 - q)⁻¹) :=
    hg.mul_left (r : ℝ)
  have hp' : HasSum (fun k : ℕ => (p : ℝ) * ((k : ℝ) * q ^ k))
      ((p : ℝ) * (q / (1 - q) ^ 2)) :=
    hn.mul_left (p : ℝ)
  have hsum := hr.add hp'
  have hsum' := hsum.mul_left ((1 / 2 : ℝ) ^ r)
  have hsum'' : HasSum
      (fun k : ℕ =>
        ((1 / 2 : ℝ) ^ r) *
          ((r : ℝ) * q ^ k + (p : ℝ) * ((k : ℝ) * q ^ k)))
      (((1 / 2 : ℝ) ^ r) *
        ((r : ℝ) * (1 - q)⁻¹ + (p : ℝ) * (q / (1 - q) ^ 2))) := by
    exact hsum'
  have hterm (k : ℕ) :
      (((r : ℝ) + (k * p : ℕ)) : ℝ) / (2 : ℝ) ^ (r + k * p) =
        ((1 / 2 : ℝ) ^ r) *
          ((r : ℝ) * q ^ k + (p : ℝ) * ((k : ℝ) * q ^ k)) := by
    have hpow : (2 : ℝ) ^ (r + k * p) =
        (2 : ℝ) ^ r * ((2 : ℝ) ^ p) ^ k := by
      rw [pow_add, Nat.mul_comm k p, pow_mul]
    have hhalf (n : ℕ) : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
      rw [div_pow]
      simp
    rw [hpow]
    dsimp [q]
    rw [hhalf r]
    have hqpow : ((1 / 2 : ℝ) ^ p) ^ k =
        1 / ((2 : ℝ) ^ p) ^ k := by
      rw [hhalf p, div_pow]
      simp
    rw [hqpow]
    push_cast
    field_simp
  have hfinal :
      ((1 / 2 : ℝ) ^ r) *
          ((r : ℝ) * (1 - q)⁻¹ + (p : ℝ) * (q / (1 - q) ^ 2)) =
        (r : ℝ) / (2 : ℝ) ^ r / (1 - ((1 / 2 : ℝ) ^ p)) +
          (p : ℝ) / (2 : ℝ) ^ r * ((1 / 2 : ℝ) ^ p) /
            (1 - ((1 / 2 : ℝ) ^ p)) ^ 2 := by
    change ((1 / 2 : ℝ) ^ r) *
        ((r : ℝ) * (1 - q)⁻¹ + (p : ℝ) * (q / (1 - q) ^ 2)) =
      (r : ℝ) / (2 : ℝ) ^ r / (1 - q) +
        (p : ℝ) / (2 : ℝ) ^ r * q / (1 - q) ^ 2
    have hhalf_r : (1 / 2 : ℝ) ^ r = 1 / (2 : ℝ) ^ r := by
      rw [div_pow]
      simp
    rw [hhalf_r]
    field_simp [ne_of_gt (sub_pos.mpr hq1)]
  have hhas : HasSum (fun k : ℕ =>
      (((r : ℝ) + (k * p : ℕ)) : ℝ) / (2 : ℝ) ^ (r + k * p))
      (((1 / 2 : ℝ) ^ r) *
        ((r : ℝ) * (1 - q)⁻¹ + (p : ℝ) * (q / (1 - q) ^ 2))) :=
    hsum''.congr_fun (fun k => hterm k)
  rw [hfinal] at hhas
  exact hhas

private lemma weighted_geometric' (p r : ℕ) (hp : 0 < p) :
    (∑' k : ℕ,
      (((r : ℝ) + (k * p : ℕ)) : ℝ) / (2 : ℝ) ^ (r + k * p)) =
      (r : ℝ) / (2 : ℝ) ^ r / (1 - ((1 / 2 : ℝ) ^ p)) +
        (p : ℝ) / (2 : ℝ) ^ r * ((1 / 2 : ℝ) ^ p) /
          (1 - ((1 / 2 : ℝ) ^ p)) ^ 2 :=
  (weighted_geometric_hasSum' p r hp).tsum_eq

theorem periodicWordSeriesIdentity (p : ℕ) (hp : 0 < p) (c : ℕ → ℤ) :
    let A : ℝ := ∑ r ∈ Finset.Icc 1 p,
      (c r : ℝ) * (2 : ℝ) ^ (p - r)
    let B : ℝ := ∑ r ∈ Finset.Icc 1 p,
      (r : ℝ) * (c r : ℝ) * (2 : ℝ) ^ (p - r)
    (∑' k : ℕ, ∑ r ∈ Finset.Icc 1 p,
      ((((r : ℝ) + (k * p : ℕ)) * (c r : ℝ)) /
        (2 : ℝ) ^ (r + k * p))) =
      (((2 : ℝ) ^ p - 1) * B + (p : ℝ) * A) /
        ((2 : ℝ) ^ p - 1) ^ 2 := by
  dsimp
  let s : Finset ℕ := Finset.Icc 1 p
  let f : ℕ → ℕ → ℝ := fun r k =>
    ((((r : ℝ) + (k * p : ℕ)) * (c r : ℝ)) /
      (2 : ℝ) ^ (r + k * p))
  have hsumr {r : ℕ} (hr : r ∈ s) : Summable (f r) := by
    have h := (weighted_geometric_hasSum' p r hp).summable
    have h' := h.mul_left ((c r : ℝ))
    apply h'.congr
    intro k
    dsimp [f]
    rw [mul_div_assoc]
    ring
  have hswap : (∑' k : ℕ, ∑ r ∈ s, f r k) =
      ∑ r ∈ s, ∑' k : ℕ, f r k := by
    simpa [s] using (Summable.tsum_finsetSum
      (s := s) (fun i hi => hsumr hi))
  rw [show (∑' k : ℕ, ∑ r ∈ Finset.Icc 1 p, f r k) = _ by rfl, hswap]
  have hinner {r : ℕ} (hr : r ∈ s) :
      ∑' k : ℕ, f r k =
        (c r : ℝ) * (r : ℝ) / (2 : ℝ) ^ r /
            (1 - ((1 / 2 : ℝ) ^ p)) +
          (c r : ℝ) * (p : ℝ) / (2 : ℝ) ^ r * ((1 / 2 : ℝ) ^ p) /
            (1 - ((1 / 2 : ℝ) ^ p)) ^ 2 := by
    dsimp [f]
    have hfun : (fun k : ℕ =>
        (((r : ℝ) + (k * p : ℕ)) * (c r : ℝ)) /
          (2 : ℝ) ^ (r + k * p)) =
        (fun k : ℕ => ((c r : ℝ)) * (((r : ℝ) + (k * p : ℕ)) /
          (2 : ℝ) ^ (r + k * p))) := by
      funext k
      ring
    rw [hfun, tsum_mul_left, weighted_geometric' p r hp]
    ring
  let q : ℝ := (1 / 2 : ℝ) ^ p
  have hq1 : q < 1 := by
    dsimp [q]
    exact pow_lt_one₀ (by norm_num) (by norm_num) hp.ne'
  have hrecipB {r : ℕ} (hr : r ∈ s) :
      (c r : ℝ) * (r : ℝ) / (2 : ℝ) ^ r =
        q * ((r : ℝ) * (c r : ℝ) * (2 : ℝ) ^ (p - r)) := by
    have hrle : r ≤ p := (Finset.mem_Icc.mp (show r ∈ Finset.Icc 1 p from hr)).2
    have hexp : p = (p - r) + r := (Nat.sub_add_cancel hrle).symm
    have hhalf : (1 / 2 : ℝ) ^ p = 1 / (2 : ℝ) ^ p := by
      rw [div_pow]
      simp
    dsimp [q]
    rw [hhalf, hexp, pow_add]
    field_simp ; simp [Nat.sub_add_cancel hrle]
  have hrecipA {r : ℕ} (hr : r ∈ s) :
      (c r : ℝ) / (2 : ℝ) ^ r =
        q * ((c r : ℝ) * (2 : ℝ) ^ (p - r)) := by
    have hrle : r ≤ p := (Finset.mem_Icc.mp (show r ∈ Finset.Icc 1 p from hr)).2
    have hexp : p = (p - r) + r := (Nat.sub_add_cancel hrle).symm
    have hhalf : (1 / 2 : ℝ) ^ p = 1 / (2 : ℝ) ^ p := by
      rw [div_pow]
      simp
    dsimp [q]
    rw [hhalf, hexp, pow_add]
    field_simp ; simp [Nat.sub_add_cancel hrle]
  have hBsum :
      (∑ r ∈ s, (c r : ℝ) * (r : ℝ) / (2 : ℝ) ^ r) =
        q * ∑ r ∈ s, (r : ℝ) * (c r : ℝ) * (2 : ℝ) ^ (p - r) := by
    rw [show (∑ r ∈ s, (c r : ℝ) * (r : ℝ) / (2 : ℝ) ^ r) =
      ∑ r ∈ s, q * ((r : ℝ) * (c r : ℝ) * (2 : ℝ) ^ (p - r)) by
        apply Finset.sum_congr rfl
        intro r hr
        exact hrecipB hr]
    rw [Finset.mul_sum]
  have hAsum :
      (∑ r ∈ s, (c r : ℝ) / (2 : ℝ) ^ r) =
        q * ∑ r ∈ s, (c r : ℝ) * (2 : ℝ) ^ (p - r) := by
    rw [show (∑ r ∈ s, (c r : ℝ) / (2 : ℝ) ^ r) =
      ∑ r ∈ s, q * ((c r : ℝ) * (2 : ℝ) ^ (p - r)) by
        apply Finset.sum_congr rfl
        intro r hr
        exact hrecipA hr]
    rw [Finset.mul_sum]
  have hsum_inner :
      (∑ r ∈ s, ∑' k : ℕ, f r k) =
        ∑ r ∈ s,
          ((c r : ℝ) * (r : ℝ) / (2 : ℝ) ^ r /
              (1 - ((1 / 2 : ℝ) ^ p)) +
            (c r : ℝ) * (p : ℝ) / (2 : ℝ) ^ r * ((1 / 2 : ℝ) ^ p) /
              (1 - ((1 / 2 : ℝ) ^ p)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hinner hr
  rw [hsum_inner]
  simp only [Finset.sum_add_distrib]
  have hfirst :
      (∑ x ∈ s, (c x : ℝ) * (x : ℝ) / (2 : ℝ) ^ x /
        (1 - ((1 / 2 : ℝ) ^ p))) =
        (∑ x ∈ s, (c x : ℝ) * (x : ℝ) / (2 : ℝ) ^ x) /
          (1 - ((1 / 2 : ℝ) ^ p)) := by
    rw [Finset.sum_div]
  have hsecond :
      (∑ x ∈ s, (c x : ℝ) * (p : ℝ) / (2 : ℝ) ^ x * ((1 / 2 : ℝ) ^ p) /
        (1 - ((1 / 2 : ℝ) ^ p)) ^ 2) =
        (p : ℝ) * ((1 / 2 : ℝ) ^ p) /
          (1 - ((1 / 2 : ℝ) ^ p)) ^ 2 *
            (∑ x ∈ s, (c x : ℝ) / (2 : ℝ) ^ x) := by
    rw [show (∑ x ∈ s, (c x : ℝ) * (p : ℝ) / (2 : ℝ) ^ x * ((1 / 2 : ℝ) ^ p) /
        (1 - ((1 / 2 : ℝ) ^ p)) ^ 2) =
      ∑ x ∈ s, ((p : ℝ) * ((1 / 2 : ℝ) ^ p) /
        (1 - ((1 / 2 : ℝ) ^ p)) ^ 2) * ((c x : ℝ) / (2 : ℝ) ^ x) by
          apply Finset.sum_congr rfl
          intro x hx
          ring]
    rw [← Finset.mul_sum]
  rw [hfirst, hsecond, hBsum, hAsum]
  let A : ℝ := ∑ r ∈ s, (c r : ℝ) * (2 : ℝ) ^ (p - r)
  let B : ℝ := ∑ r ∈ s, (r : ℝ) * (c r : ℝ) * (2 : ℝ) ^ (p - r)
  change q * B / (1 - q) +
      (p : ℝ) * q / (1 - q) ^ 2 * (q * A) =
    (((2 : ℝ) ^ p - 1) * B + (p : ℝ) * A) /
      ((2 : ℝ) ^ p - 1) ^ 2
  have hhalf : (1 / 2 : ℝ) ^ p = 1 / (2 : ℝ) ^ p := by
    norm_num [div_pow]
  dsimp [q]
  rw [hhalf]
  field_simp

end MathlibPlus.NumberTheory.Claim35773
