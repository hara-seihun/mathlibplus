import Mathlib

namespace MathlibPlus.Algebra.Claim33032

/-- The binomial expansion underlying the scalar-power normalizer identity. -/
theorem scalarPowerDifference_expansion
    {R : Type*} [CommRing R] (m : ℕ) (s x : R) :
    ((1 + s * x)^m - 1) - s * ((1 + x)^m - 1) =
      ∑ k ∈ Finset.Icc 1 m, (m.choose k : R) * (s^k - s) * x^k := by
  have hpow (a : R) :
      (1 + a) ^ m - 1 = ∑ k ∈ Finset.Icc 1 m, (m.choose k : R) * a ^ k := by
    have h : (a + 1)^m = ∑ k ∈ Finset.range (m + 1), a^k * (m.choose k : R) := by
      simpa [one_pow, mul_one] using (add_pow a 1 m)
    have hsub := congrArg (fun z : R => z - 1) h
    have hsum :
        (∑ k ∈ Finset.Icc 1 m, a^k * (m.choose k : R)) =
          (∑ k ∈ Finset.range (m + 1), a^k * (m.choose k : R)) -
            (∑ k ∈ Finset.range 1, a^k * (m.choose k : R)) := by
      rw [← Finset.Ico_succ_right_eq_Icc 1 m]
      exact Finset.sum_Ico_eq_sub (f := fun k : ℕ => a^k * (m.choose k : R))
        (show 1 ≤ m + 1 by omega)
    calc
      (1 + a)^m - 1 = (∑ k ∈ Finset.range (m + 1), a^k * (m.choose k : R)) - 1 := by
        simpa [add_comm] using hsub
      _ = (∑ k ∈ Finset.range (m + 1), a^k * (m.choose k : R)) -
            (∑ k ∈ Finset.range 1, a^k * (m.choose k : R)) := by
        simp
      _ = ∑ k ∈ Finset.Icc 1 m, a^k * (m.choose k : R) := by
        rw [hsum]
      _ = ∑ k ∈ Finset.Icc 1 m, (m.choose k : R) * a^k := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [hpow (s*x), hpow x]
  simp_rw [mul_pow]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Under the pointwise scalar-linearity relation, the expansion is zero. -/
theorem scalarPowerLinearity_forces_expansion
    {R : Type*} [CommRing R] (m : ℕ) (s x : R)
    (h : (1 + s * x)^m - 1 = s * ((1 + x)^m - 1)) :
    0 = ∑ k ∈ Finset.Icc 1 m, (m.choose k : R) * (s^k - s) * x^k := by
  rw [← scalarPowerDifference_expansion m s x]
  exact (sub_eq_zero.mpr h).symm

end MathlibPlus.Algebra.Claim33032
