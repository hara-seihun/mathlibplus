import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Combinatorics

/-- The two-subset incidence numbers in the dense-support calculation obey the
adjacent-binomial ratio used for the pairwise overlap. -/
private lemma choose_adjacent_ratio
    (m t : ℕ) (hm : 3 ≤ m) (ht : 2 ≤ t) (_htm : t ≤ m) :
    (Nat.choose (m - 1) (t - 1) : ℚ) * ((t - 1 : ℕ) : ℚ) =
      ((m - 1 : ℕ) : ℚ) * (Nat.choose (m - 2) (t - 2) : ℚ) := by
  have h := Nat.choose_mul (n := m - 1) (k := t - 1) (s := 1) (by omega)
  have hm1sub : m - 1 - 1 = m - 2 := by omega
  have ht1sub : t - 1 - 1 = t - 2 := by omega
  rw [hm1sub, ht1sub] at h
  have h' :
      Nat.choose (m - 1) (t - 1) * (t - 1) =
        (m - 1) * Nat.choose (m - 2) (t - 2) := by
    simpa [Nat.choose_one_right] using h
  exact_mod_cast h'

/-- Exact arithmetic core of claim 36665.  The incidence-carrier sentence in
that packet is represented by its uniformity `n`, pair-overlap `λ`, and pivot
average `μ`; all displayed divisions are in `ℚ`. -/
theorem denseBalancedSupportArithmetic
    (m t : ℕ) (hm : 3 ≤ m) (ht : 2 ≤ t) (htm : t ≤ m) :
    let n : ℚ := Nat.choose (m - 1) (t - 1)
    let lam : ℚ := Nat.choose (m - 2) (t - 2)
    let mu : ℚ := (n + (m - 1) * lam) / m
    lam = n * ((t - 1 : ℕ) : ℚ) / ((m - 1 : ℕ) : ℚ) ∧
      mu = n * (t : ℚ) / (m : ℚ) := by
  dsimp
  have hratioNat := choose_adjacent_ratio m t hm ht htm
  have hratio := hratioNat
  have hmcast : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have htcast : ((t - 1 : ℕ) : ℚ) = (t : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hmcast, htcast] at hratio
  have hm1 : (m : ℚ) - 1 ≠ 0 := by
    have h : (1 : ℚ) < (m : ℚ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  constructor
  · field_simp [hm1]
    simpa [mul_comm] using hratioNat.symm
  · field_simp [hm1, hm0]
    linear_combination hratio.symm

/-- At the balanced choice `t=floor(m/2)`, the density fraction is at least
one third.  The lower boundary `m=3` is included; the pair-overlap formula
above is used when `m≥4`, where `t≥2`. -/
theorem denseBalancedSupportAtHalf
    (m : ℕ) (hm : 3 ≤ m) :
    (1 / 3 : ℚ) ≤ ((m / 2 : ℕ) : ℚ) / (m : ℚ) := by
  have hmul : m ≤ 3 * (m / 2) := by omega
  have hm0 : (m : ℚ) > 0 := by positivity
  field_simp [hm0]
  exact_mod_cast hmul

end MathlibPlus.Combinatorics
