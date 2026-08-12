import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim3156

noncomputable section

/-- The dyadic weight used in the finite-representation claim. -/
def weight (n : ℕ) : ℚ := (n : ℚ) / (2 : ℚ) ^ n

/-- A finite representation of `weight n` by distinct later indices.  The
finite digit function is read at offsets `1,...,m`; the bound `e ≤ 1` makes
these digits Boolean, and `e m = 1` records that `m` is the last offset. -/
def finiteRepresentation (n : ℕ) : Prop :=
  ∃ (m : ℕ) (e : ℕ → ℕ),
    1 ≤ m ∧
    (∀ i < m, e (i + 1) ≤ 1) ∧
    e m = 1 ∧
    2 ≤ ∑ i ∈ Finset.range m, e (i + 1) ∧
    weight n = ∑ i ∈ Finset.range m,
      (e (i + 1) : ℚ) * weight (n + i + 1)

/-- An integer carry path for the same finite digit list. -/
def carryCertificate (n : ℕ) : Prop :=
  ∃ (m : ℕ) (e : ℕ → ℕ) (R : ℕ → ℤ),
    1 ≤ m ∧
    (∀ i < m, e (i + 1) ≤ 1) ∧
    e m = 1 ∧
    2 ≤ ∑ i ∈ Finset.range m, e (i + 1) ∧
    R 0 = n ∧
    R m = 0 ∧
    (∀ i < m,
      R (i + 1) = 2 * R i - (n + i + 1 : ℤ) * e (i + 1))

private lemma residual_identity
    (n m : ℕ) (e : ℕ → ℕ) (R : ℕ → ℤ)
    (hR0 : R 0 = n)
    (hrec : ∀ i < m,
      R (i + 1) = 2 * R i - (n + i + 1 : ℤ) * e (i + 1)) :
    (R m : ℚ) / (2 : ℚ) ^ (n + m) =
      weight n - ∑ i ∈ Finset.range m,
        (e (i + 1) : ℚ) * weight (n + i + 1) := by
  induction m with
  | zero =>
      simp [weight, hR0]
  | succ m ih =>
      have hrec_m := hrec m (Nat.lt_succ_self m)
      have hrec_prev : ∀ i < m,
          R (i + 1) = 2 * R i - (n + i + 1 : ℤ) * e (i + 1) := by
        intro i hi
        exact hrec i (Nat.lt_trans hi (Nat.lt_succ_self m))
      have ih' := ih hrec_prev
      rw [Finset.sum_range_succ]
      rw [hrec_m]
      rw [show n + (m + 1) = n + m + 1 by omega]
      calc
        (Int.cast (2 * R m - (n + m + 1 : ℤ) * e (m + 1)) : ℚ) /
              (2 : ℚ) ^ (n + m + 1) =
            (Int.cast (R m) : ℚ) / (2 : ℚ) ^ (n + m) -
              (e (m + 1) : ℚ) * (n + m + 1 : ℚ) /
                (2 : ℚ) ^ (n + m + 1) := by
          rw [pow_succ]
          push_cast
          field_simp
        _ = (weight n - ∑ i ∈ Finset.range m,
              (e (i + 1) : ℚ) * weight (n + i + 1)) -
              (e (m + 1) : ℚ) * (n + m + 1 : ℚ) /
                (2 : ℚ) ^ (n + m + 1) := by
          rw [ih']
        _ = weight n - (∑ i ∈ Finset.range m,
              (e (i + 1) : ℚ) * weight (n + i + 1) +
              (e (m + 1) : ℚ) * weight (n + m + 1)) := by
          simp [weight]
          ring

/-- A reverse predecessor exists exactly when the reverse numerator is even. -/
theorem reverse_predecessor_even_claim3156 (n d e : ℕ) (r : ℤ) :
    (∃ q : ℤ, 2 * q = r + (n + d : ℤ) * e) ↔
      Even (r + (n + d : ℤ) * e) := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    linarith
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    linarith

/-- The exact forward/reverse-carry equivalence from R-3156. -/
theorem finiteRepresentation_iff_carryCertificate (n : ℕ) (_hn : 3 ≤ n) :
    finiteRepresentation n ↔ carryCertificate n := by
  constructor
  · rintro ⟨m, e, hm, hbits, hlast, hcard, hsum⟩
    let R : ℕ → ℤ := fun d =>
      Nat.rec (n : ℤ)
        (fun d r => 2 * r - (n + d + 1 : ℤ) * e (d + 1)) d
    have hR0 : R 0 = n := by
      simp [R]
    have hrec : ∀ i < m,
        R (i + 1) = 2 * R i - (n + i + 1 : ℤ) * e (i + 1) := by
      intro i hi
      simp [R]
    have hres := residual_identity n m e R hR0 hrec
    have hRm_rat : (Int.cast (R m) : ℚ) = 0 := by
      have hzero : (Int.cast (R m) : ℚ) / (2 : ℚ) ^ (n + m) = 0 := by
        rw [hres, hsum]
        ring
      rcases (div_eq_zero_iff).mp hzero with h | h
      · exact h
      · norm_num at h
    have hRm : R m = 0 := by
      exact_mod_cast hRm_rat
    exact ⟨m, e, R, hm, hbits, hlast, hcard, hR0, hRm, hrec⟩
  · rintro ⟨m, e, R, hm, hbits, hlast, hcard, hR0, hRm, hrec⟩
    have hres := residual_identity n m e R hR0 hrec
    have hzero : weight n - ∑ i ∈ Finset.range m,
        (e (i + 1) : ℚ) * weight (n + i + 1) = 0 := by
      rw [← hres, hRm]
      norm_num
    exact ⟨m, e, hm, hbits, hlast, hcard, by linarith⟩

private lemma family_power_bound : ∀ m : ℕ, 2 ≤ m → m + 5 ≤ 2 ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro hm
      by_cases hsmall : m < 2
      · have hm_eq : m = 1 := by omega
        subst m
        norm_num
      · have ihm : m + 5 ≤ 2 ^ (m + 1) := ih (by omega)
        rw [show Nat.succ m + 1 = (m + 1) + 1 by omega, pow_succ]
        omega

/-- The consecutive support `{1,...,m}` gives the source's infinite family. -/
theorem consecutive_family_representation (m : ℕ) (hm : 2 ≤ m) :
    finiteRepresentation (2 ^ (m + 1) - m - 2) := by
  let n : ℕ := 2 ^ (m + 1) - m - 2
  have hbound : m + 5 ≤ 2 ^ (m + 1) := family_power_bound m hm
  have hn : 3 ≤ n := by
    dsimp [n]
    omega
  apply (finiteRepresentation_iff_carryCertificate n hn).2
  let R : ℕ → ℤ := fun d =>
    (n : ℤ) - (2 : ℤ) ^ (d + 1) + d + 2
  refine ⟨m, (fun _ => 1), R, by omega, ?_, by simp, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp
  · simp; omega
  · dsimp [R]
    simp
  · have hsub : 2 ^ (m + 1) - m - 2 = 2 ^ (m + 1) - (m + 2) := by
      omega
    have hcast : ((n : ℤ) = (2 : ℤ) ^ (m + 1) - m - 2) := by
      dsimp [n]
      rw [hsub, Nat.cast_sub (by omega)]
      push_cast
      ring
    dsimp [R]
    rw [hcast]
    ring
  · intro i hi
    dsimp [R]
    rw [show i + 1 + 1 = (i + 1) + 1 by omega, pow_succ]
    ring

/-- The exceptional initial identity recorded in R-3156. -/
theorem initial_witness_claim3156 :
    weight 1 = weight 2 ∧ weight 1 = weight 4 + weight 5 + weight 6 := by
  norm_num [weight]

end
end MathlibPlus.NumberTheory.Claim3156
