import MathlibPlus.Open.Basic

namespace MathlibPlus.NumberTheory

private theorem prime_power_log_separation_claim12262
    {k l : ℤ}
    (hlog : (k.natAbs : ℝ) * Real.log 3 =
      (l.natAbs : ℝ) * Real.log 2) :
    l = 0 := by
  have hpowlog : Real.log ((3 : ℝ) ^ k.natAbs) =
      Real.log ((2 : ℝ) ^ l.natAbs) := by
    rw [Real.log_pow, Real.log_pow]
    exact hlog
  have hpowreal : (3 : ℝ) ^ k.natAbs = (2 : ℝ) ^ l.natAbs :=
    Real.log_injOn_pos
      (show 0 < (3 : ℝ) ^ k.natAbs from by positivity)
      (show 0 < (2 : ℝ) ^ l.natAbs from by positivity)
      hpowlog
  have hpow : 3 ^ k.natAbs = 2 ^ l.natAbs := by
    exact_mod_cast hpowreal
  by_contra hl
  have hlpos : 0 < l.natAbs := Int.natAbs_pos.mpr hl
  have hdivpow : 2 ∣ 3 ^ k.natAbs := by
    rw [hpow]
    exact dvd_pow_self 2 (Nat.ne_of_gt hlpos)
  have hdiv : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow hdivpow
  norm_num at hdiv

/-- The two integer support lattices with periods `log 2` and `log 3` meet
only at zero.  This is the real form of the common-frequency assertion in
claim 12262; multiplication by the nonzero factor `2πi` is injective. -/
theorem support_lattice_intersection_claim12262
    {k l : ℤ}
    (h : (2 * Real.pi * (k : ℝ)) / Real.log 2 =
      (2 * Real.pi * (l : ℝ)) / Real.log 3) :
    k = 0 ∧ l = 0 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hcross' : (2 * Real.pi * (k : ℝ)) * Real.log 3 =
      (2 * Real.pi * (l : ℝ)) * Real.log 2 :=
    (div_eq_div_iff (ne_of_gt hlog2) (ne_of_gt hlog3)).mp h
  have hzero : (2 * Real.pi) *
      ((k : ℝ) * Real.log 3 - (l : ℝ) * Real.log 2) = 0 := by
    calc
      (2 * Real.pi) * ((k : ℝ) * Real.log 3 -
          (l : ℝ) * Real.log 2) =
          (2 * Real.pi * (k : ℝ)) * Real.log 3 -
            (2 * Real.pi * (l : ℝ)) * Real.log 2 := by ring
      _ = 0 := sub_eq_zero.mpr hcross'
  have hcross : (k : ℝ) * Real.log 3 =
      (l : ℝ) * Real.log 2 := by
    rcases mul_eq_zero.mp hzero with hpi | hcross
    · exact (ne_of_gt (mul_pos (by norm_num) Real.pi_pos) hpi).elim
    · exact sub_eq_zero.mp hcross
  have habs := congrArg abs hcross
  have hkabs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    simpa using (congrArg (fun n : ℤ => (n : ℝ)) (Int.natCast_natAbs k)).symm
  have hlabs : |(l : ℝ)| = (l.natAbs : ℝ) := by
    simpa using (congrArg (fun n : ℤ => (n : ℝ)) (Int.natCast_natAbs l)).symm
  have hlogabs : (k.natAbs : ℝ) * Real.log 3 =
      (l.natAbs : ℝ) * Real.log 2 := by
    calc
      (k.natAbs : ℝ) * Real.log 3 =
          |(k : ℝ)| * |Real.log 3| := by rw [hkabs, abs_of_pos hlog3]
      _ = |(k : ℝ) * Real.log 3| := (abs_mul _ _).symm
      _ = |(l : ℝ) * Real.log 2| := habs
      _ = |(l : ℝ)| * |Real.log 2| := abs_mul _ _
      _ = (l.natAbs : ℝ) * Real.log 2 := by rw [hlabs, abs_of_pos hlog2]
  have hl0 : l = 0 := prime_power_log_separation_claim12262 hlogabs
  have hkreal : (k : ℝ) = 0 := by
    have : (k : ℝ) * Real.log 3 = 0 := by simpa [hl0] using hcross
    exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hlog3)
  exact ⟨by exact_mod_cast hkreal, hl0⟩

end MathlibPlus.NumberTheory
