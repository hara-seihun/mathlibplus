import Mathlib

namespace MathlibPlus.Analysis.BesselK

/-- Standard integral normalization of the real Bessel `J` function at
nonnegative integer order.  The pinned mathlib has no canonical declaration
for this function. -/
noncomputable def besselJ (n : ℕ) (y : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in Set.Icc 0 Real.pi,
    Real.cos ((n : ℝ) * θ - y * Real.sin θ)

/-- The centered kernels used in claims 4045 and 4052. -/
noncomputable def centeredKernel (r : ℕ) (x t : ℝ) : ℝ :=
  match r with
  | 0 => Real.sqrt (x / t) * besselJ 1 (2 * Real.sqrt (x * t))
  | n + 1 =>
      (-1 : ℝ) ^ n * Real.rpow (t / x) ((n : ℝ) / 2) *
        besselJ n (2 * Real.sqrt (x * t))

theorem centeredKernel_bound_of_besselJ_bound
    (hJ : ∀ (n : ℕ) (y : ℝ), |besselJ n y| ≤ 1)
    (r : ℕ) (hr : 1 ≤ r) (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    |centeredKernel r x t| ≤
      Real.rpow (t / x) (((r : ℝ) - 1) / 2) := by
  cases r with
  | zero => omega
  | succ n =>
    simp only [centeredKernel]
    have hpow : 0 ≤ Real.rpow (t / x) ((n : ℝ) / 2) := by
      exact Real.rpow_nonneg (le_of_lt (div_pos ht hx)) _
    have habs : |(-1 : ℝ) ^ n| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [abs_mul, abs_mul, habs]
    simp only [one_mul]
    have hj := hJ n (2 * Real.sqrt (x * t))
    have he : (((n + 1 : ℕ) : ℝ) - 1) / 2 = (n : ℝ) / 2 := by
      norm_num [Nat.cast_add, Nat.cast_one]
    rw [he]
    rw [abs_of_nonneg hpow]
    exact mul_le_of_le_one_right hpow hj

theorem centeredKernel_zero_bound_of_besselJ_bound
    (hJ : ∀ (n : ℕ) (y : ℝ), |besselJ n y| ≤ 1)
    (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    |centeredKernel 0 x t| ≤ Real.rpow (t / x) (-1 / 2 : ℝ) := by
  have hroot : Real.sqrt (x / t) = Real.rpow (t / x) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow (le_of_lt hx) (le_of_lt ht)]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
    change x ^ (1 / 2 : ℝ) / t ^ (1 / 2 : ℝ) =
      (t / x) ^ (-(1 / 2 : ℝ))
    rw [Real.rpow_neg (by positivity)]
    rw [Real.div_rpow (le_of_lt ht) (le_of_lt hx)]
    field_simp [ne_of_gt hx, ne_of_gt ht]
  simp only [centeredKernel]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), hroot]
  have hpow : 0 ≤ Real.rpow (t / x) (-1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (le_of_lt (div_pos ht hx)) _
  exact mul_le_of_le_one_right hpow (hJ 1 (2 * Real.sqrt (x * t)))

end MathlibPlus.Analysis.BesselK

namespace MathlibPlus.Open.Analysis.BesselK

open MathlibPlus.Analysis.BesselK

/-- Claim 4052.  The standard Bessel `J` is anchored to the integral
normalization above; its elementary bound is retained as the explicit premise
that yields the two displayed kernel bounds. -/
def integerOrderKernelBounds : Prop :=
  (∀ (n : ℕ) (y : ℝ), |besselJ n y| ≤ 1) →
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (x t : ℝ), 0 < x → 0 < t →
      |centeredKernel r x t| ≤
          Real.rpow (t / x) (((r : ℝ) - 1) / 2) ∧
      |centeredKernel (r - 1) x t| ≤
          Real.rpow (t / x) (((r : ℝ) - 2) / 2)

end MathlibPlus.Open.Analysis.BesselK

namespace MathlibPlus.Analysis.BesselK

theorem integerOrderKernelBounds_proved :
    MathlibPlus.Open.Analysis.BesselK.integerOrderKernelBounds := by
  intro hJ r hr x t hx ht
  constructor
  · exact centeredKernel_bound_of_besselJ_bound hJ r hr x t hx ht
  · cases r with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        have h := centeredKernel_zero_bound_of_besselJ_bound hJ x t hx ht
        convert h using 1 <;> norm_num [Nat.cast_add, Nat.cast_one]
      | succ m =>
        have h := centeredKernel_bound_of_besselJ_bound hJ (m + 1) (by omega) x t hx ht
        convert h using 1
        · norm_num
        · norm_num [Nat.cast_add, Nat.cast_one]
          congr 1
          ring

end MathlibPlus.Analysis.BesselK
