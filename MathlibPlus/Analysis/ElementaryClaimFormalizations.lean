import Mathlib

namespace MathlibPlus.Analysis.ElementaryClaimFormalizations

/-- Claim 15655: the norm of an exterior-square determinant is bounded by the
sum of the norms of its two monomials. -/
theorem exteriorSquareNormBound (x y z : ℂ) :
    ‖x * z - y ^ 2‖ ≤ ‖x‖ * ‖z‖ + ‖y‖ ^ 2 := by
  calc
    ‖x * z - y ^ 2‖ ≤ ‖x * z‖ + ‖y ^ 2‖ := norm_sub_le _ _
    _ = ‖x‖ * ‖z‖ + ‖y‖ ^ 2 := by rw [norm_mul, norm_pow]

/-- Claim 2319: the endpoint multiplier has the stated elementary bounds. -/
theorem endpointMultiplierInequality (m : ℕ) (s : ℝ)
    (_hm : 1 ≤ m) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ 1 - (1 - s) ^ m ∧ 1 - (1 - s) ^ m ≤ (m : ℝ) * s := by
  have hq0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hq1 : 1 - s ≤ 1 := by linarith
  have hpow_le : ∀ k : ℕ, (1 - s) ^ k ≤ 1 :=
    fun k => pow_le_one₀ hq0 hq1
  have hpow_nonneg : ∀ k : ℕ, 0 ≤ (1 - s) ^ k :=
    fun k => pow_nonneg hq0 k
  have hbound : ∀ k : ℕ,
      0 ≤ 1 - (1 - s) ^ k ∧ 1 - (1 - s) ^ k ≤ (k : ℝ) * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hdecomp :
            1 - (1 - s) ^ k * (1 - s) =
              (1 - (1 - s) ^ k) + (1 - s) ^ k * s := by
          ring
        rw [hdecomp]
        constructor
        · exact add_nonneg ih.1 (mul_nonneg (hpow_nonneg k) hs0)
        · have hmul : (1 - s) ^ k * s ≤ s := by
            calc
              (1 - s) ^ k * s ≤ 1 * s :=
                mul_le_mul_of_nonneg_right (hpow_le k) hs0
              _ = s := one_mul s
          calc
            (1 - (1 - s) ^ k) + (1 - s) ^ k * s
                ≤ (k : ℝ) * s + s := add_le_add ih.2 hmul
            _ = ((k + 1 : ℕ) : ℝ) * s := by
              norm_num [Nat.cast_add]
              ring
  exact hbound m

/-- Claim 18064: the displayed numerator vanishes at both endpoints. -/
theorem cancellationAtZeroAndOne (n : ℕ) (hn : 1 ≤ n) :
    let F : ℝ → ℝ := fun s =>
      ((n : ℝ) + s) * ((n + 1 : ℕ) : ℝ) ^ (-s) -
        (n : ℝ) ^ (1 - s)
    F 0 = 0 ∧ F 1 = 0 := by
  dsimp
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  constructor
  · simp [Real.rpow_zero]
  · rw [show (-(1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
      show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero]
    field_simp
    norm_num [Nat.cast_add]

/--
Claim 7237: on one composed Dirichlet-series summand, the shared dilation
logarithm cancels under the ordered difference of the two logarithmic
parameters.  The constant term contributes the final `-c` factor.
-/
theorem orderedLogDifferentialKernel_claim7237
    (n m d : ℕ) (w v c : ℝ)
    (_hn : 0 < n) (_hm : 0 < m) (_hd : 0 < d) :
    let term : ℝ → ℝ → ℝ := fun w v =>
      Real.exp
        (-w * (Real.log (n : ℝ) + Real.log (d : ℝ)) -
          v * (Real.log (m : ℝ) + Real.log (d : ℝ)))
    deriv (fun w' => term w' v) w - deriv (fun v' => term w v') v - c * term w v =
      (Real.log (m : ℝ) - Real.log (n : ℝ) - c) * term w v := by
  dsimp
  let an : ℝ := Real.log (n : ℝ) + Real.log (d : ℝ)
  let am : ℝ := Real.log (m : ℝ) + Real.log (d : ℝ)
  have hinner_w :
      HasDerivAt (fun x : ℝ => -x * an - v * am) (-an) w := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id w).const_mul (-an)).sub_const (v * am))
  have hinner_v :
      HasDerivAt (fun x : ℝ => -w * an - x * am) (-am) v := by
    convert ((hasDerivAt_const v (-w * an)).sub
      ((hasDerivAt_id v).const_mul am)) using 1 <;> try rfl
    · funext x
      simp only [Pi.sub_apply, id_eq]
      ring
    · ring
  have hw := (Real.hasDerivAt_exp (-w * an - v * am)).comp w hinner_w
  have hv := (Real.hasDerivAt_exp (-w * an - v * am)).comp v hinner_v
  have hderiv_w :
      deriv (fun x : ℝ => Real.exp (-x * an - v * am)) w =
        Real.exp (-w * an - v * am) * (-an) := by
    simpa using hw.deriv
  have hderiv_v :
      deriv (fun x : ℝ => Real.exp (-w * an - x * am)) v =
        Real.exp (-w * an - v * am) * (-am) := by
    simpa using hv.deriv
  rw [hderiv_w, hderiv_v]
  dsimp [an, am]
  ring

end MathlibPlus.Analysis.ElementaryClaimFormalizations
