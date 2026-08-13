import MathlibPlus.Basic

namespace MathlibPlus.Algebra.PullFirstRecurrenceClaims

theorem claim13264_iterate_pow_three (β : ℝ) (n : ℕ) :
    (fun x : ℝ => x ^ 3)^[n] β = β ^ (3 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih, ← pow_mul, pow_succ]

theorem claim51440_collision_closed_form
    (M : ℝ) (hM : 0 < M) (p : ℕ → ℝ)
    (h0 : p 0 = 1 / M)
    (hrec : ∀ ℓ : ℕ, p (ℓ + 1) = p ℓ + (1 - p ℓ) / M) :
    ∀ L : ℕ, p L = 1 - (1 - 1 / M) ^ (L + 1) := by
  have hM0 : M ≠ 0 := ne_of_gt hM
  intro L
  induction L with
  | zero => simpa using h0
  | succ L ih =>
      calc
        p (Nat.succ L) = p L + (1 - p L) / M := by
          simpa [Nat.succ_eq_add_one] using hrec L
        _ = (1 - (1 - 1 / M) ^ (L + 1)) +
              (1 - (1 - (1 - 1 / M) ^ (L + 1))) / M := by rw [ih]
        _ = 1 - (1 - 1 / M) ^ (Nat.succ L + 1) := by
          simp only [Nat.succ_eq_add_one, pow_succ]
          ring

theorem claim51440_barycentre_variance (n pL : ℝ) (hn : n ≠ 0) :
    (1 + (n - 1) * pL) / n = pL + (1 - pL) / n := by
  field_simp [hn]
  ring

theorem claim53233_closed_forms
    (a b : ℕ → ℚ)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : ∀ r : ℕ,
      a (r + 1) - a r = (135 * ((r + 1 : ℕ) : ℚ) - 3) / 64)
    (hb : ∀ r : ℕ,
      b (r + 1) =
        (5 * (((r + 1 : ℕ) : ℚ) ^ 2) + 77 * ((r + 1 : ℕ) : ℚ) - 2) / 32
          + (3 / 4 : ℚ) * b r + (1 / 4 : ℚ) * a r) :
    ∀ r : ℕ,
      a r = 3 * (r : ℚ) * (45 * (r : ℚ) + 43) / 128 ∧
      b r = (215 * (r : ℚ) ^ 2 - 199 * (r : ℚ) + 1216) / 128
        - (19 / 2 : ℚ) * (3 / 4 : ℚ) ^ r := by
  intro r
  induction r with
  | zero =>
      constructor
      · simpa using ha0
      · norm_num [hb0]
  | succ r ih =>
      constructor
      · have h := ha r
        have hs : a (Nat.succ r) = a r +
            (135 * ((r + 1 : ℕ) : ℚ) - 3) / 64 := by
          simpa [Nat.succ_eq_add_one, add_comm] using (sub_eq_iff_eq_add.mp h)
        rw [hs, ih.1]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      · have h := hb r
        have hs : b (Nat.succ r) =
            (5 * (((r + 1 : ℕ) : ℚ) ^ 2) + 77 * ((r + 1 : ℕ) : ℚ) - 2) / 32
              + (3 / 4 : ℚ) * b r + (1 / 4 : ℚ) * a r := by
          simpa [Nat.succ_eq_add_one] using h
        rw [hs, ih.2, ih.1, pow_succ]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring

theorem claim53233_budget (n : ℕ) (hn : 1 ≤ n) :
    ((215 * (n : ℚ) ^ 2 - 199 * (n : ℚ) + 1216) / 128
        - (19 / 2 : ℚ) * (3 / 4 : ℚ) ^ n) / (n : ℚ) ^ 2 ≤ 5 / 2 := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  · have hn3 : (3 : ℚ) ≤ (n + 3 : ℕ) := by norm_num
    have hx2 : (9 : ℚ) ≤ ((n + 3 : ℕ) : ℚ) ^ 2 := by nlinarith
    have hpoly : 0 ≤ 105 * ((n + 3 : ℕ) : ℚ) ^ 2 +
        199 * ((n + 3 : ℕ) : ℚ) - 1216 := by nlinarith
    have hgeom : 0 ≤ (19 / 2 : ℚ) * (3 / 4 : ℚ) ^ (n + 3) := by positivity
    have hnpos : 0 < ((n + 3 : ℕ) : ℚ) ^ 2 := by positivity
    apply (div_le_iff₀ hnpos).2
    nlinarith

end MathlibPlus.Algebra.PullFirstRecurrenceClaims
