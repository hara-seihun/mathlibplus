import Mathlib

namespace MathlibPlus.NumberTheory.Claim19163

/-- The finite, exact divisor-fibre form of the reindexing `k = mn`, `d = m`.
The hypotheses needed to rearrange an infinite double sum are deliberately not
hidden: this theorem handles one positive product shell. -/
theorem divisorFiber_reindex
    (k : ℕ) (hk : 0 < k) (u : ℝ) (F : ℕ → ℝ → ℝ) :
    (∑ m ∈ k.divisors,
        F k (u + Real.log (m : ℝ) - (1 / 2 : ℝ) * Real.log (k : ℝ))) =
      (∑ p ∈ k.divisorsAntidiagonal,
        F (p.1 * p.2)
          (u + (1 / 2 : ℝ) * Real.log ((p.1 : ℝ) / (p.2 : ℝ)))) := by
  apply Finset.sum_bij (fun m _ => (m, k / m))
  · intro m hm
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, Nat.ne_of_gt hk⟩
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hm)
  · intro m₁ hm₁ m₂ hm₂ h
    exact congrArg Prod.fst h
  · intro p hp
    have hprod : p.1 * p.2 = k :=
      (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hp1div : p.1 ∣ k := by
      rw [← hprod]
      exact dvd_mul_right p.1 p.2
    have hp1pos : 0 < p.1 := Nat.pos_of_dvd_of_pos hp1div hk
    have hquot : k / p.1 = p.2 := by
      apply Nat.div_eq_of_eq_mul_left hp1pos
      simpa [Nat.mul_comm] using hprod.symm
    refine ⟨p.1, (Nat.mem_divisors.mpr ⟨hp1div, hk0⟩), ?_⟩
    exact Prod.ext rfl hquot
  · intro m hm
    have hdiv : m ∣ k := Nat.dvd_of_mem_divisors hm
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hdiv hk
    have hqpos : 0 < k / m := Nat.div_pos (Nat.le_of_dvd hk hdiv) hmpos
    have hprod : m * (k / m) = k := Nat.mul_div_cancel' hdiv
    have hlogs : Real.log (k : ℝ) =
        Real.log (m : ℝ) + Real.log ((k / m : ℕ) : ℝ) := by
      rw [show (k : ℝ) = (m : ℝ) * ((k / m : ℕ) : ℝ) by
        exact_mod_cast hprod.symm, Real.log_mul]
      · positivity
      · positivity
    have harg : u + Real.log (m : ℝ) - (1 / 2 : ℝ) * Real.log (k : ℝ) =
        u + (1 / 2 : ℝ) *
          Real.log ((m : ℝ) / ((k / m : ℕ) : ℝ)) := by
      rw [Real.log_div]
      · rw [hlogs]
        ring
      · positivity
      · positivity
    rw [harg]
    congr 1
    exact hprod.symm

end MathlibPlus.NumberTheory.Claim19163
