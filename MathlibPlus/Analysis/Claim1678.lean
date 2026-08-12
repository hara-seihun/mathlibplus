import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace MathlibPlus.Analysis.Claim1678

/-- The strict B-side tail condition forces positive `t` and the exponential
lower bound on `K`. -/
theorem direct_tail_condition_requires_positive_time_and_exponential_bound
    {K N t : ℝ} (hK : 1 ≤ K) (_hN : 0 < N)
    (hfrac0 : 0 < 1 - K / N) (hfrac1 : 1 - K / N < 1)
    (hcond : (t / 2) * Real.log K * (1 - K / N) > 1) :
    0 < t ∧ Real.exp (2 / t) < K := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hlog_nonneg : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlog_pos : 0 < Real.log K := by
    by_contra h
    have hlog_zero : Real.log K = 0 := le_antisymm (le_of_not_gt h) hlog_nonneg
    rw [hlog_zero] at hcond
    norm_num at hcond
  have ht_pos : 0 < t := by
    by_contra h
    have ht_nonpos : t ≤ 0 := le_of_not_gt h
    have hfirst_nonpos : t / 2 * Real.log K ≤ 0 := by
      have : t / 2 ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg this hlog_nonneg
    have hprod_nonpos : t / 2 * Real.log K * (1 - K / N) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hfirst_nonpos (le_of_lt hfrac0)
    linarith
  have hfirst_pos : 0 < t / 2 * Real.log K :=
    mul_pos (by positivity) hlog_pos
  have hfirst_gt : 1 < t / 2 * Real.log K := by
    by_contra h
    have hfirst_le : t / 2 * Real.log K ≤ 1 := le_of_not_gt h
    have hprod_le : t / 2 * Real.log K * (1 - K / N) ≤
        t / 2 * Real.log K * 1 := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hfrac1) (le_of_lt hfirst_pos)
    linarith
  have hlog_bound : 2 / t < Real.log K := by
    apply (div_lt_iff₀ ht_pos).2
    nlinarith [hfirst_gt]
  exact ⟨ht_pos, (Real.lt_log_iff_exp_lt hKpos).mp hlog_bound⟩

/-- An upper bound `K ≤ M` turns the exponential lower bound into the
corresponding strict lower bound on `t`. -/
theorem direct_tail_condition_requires_upper_threshold
    {K N t M : ℝ} (hK : 1 ≤ K) (_hN : 0 < N)
    (hfrac0 : 0 < 1 - K / N) (hfrac1 : 1 - K / N < 1)
    (hcond : (t / 2) * Real.log K * (1 - K / N) > 1)
    (hKM : K ≤ M) (hM : 1 < M) :
    2 / Real.log M < t := by
  have hbase := direct_tail_condition_requires_positive_time_and_exponential_bound
    hK _hN hfrac0 hfrac1 hcond
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_of_lt hM)
  have hlogMpos : 0 < Real.log M := Real.log_pos hM
  have hexpM : Real.exp (2 / t) < M := lt_of_lt_of_le hbase.2 hKM
  have h2t_logM : 2 / t < Real.log M :=
    (Real.lt_log_iff_exp_lt hMpos).mpr hexpM
  apply (div_lt_iff₀ hlogMpos).2
  have hmul : 2 < Real.log M * t := (div_lt_iff₀ hbase.1).mp h2t_logM
  nlinarith [hmul]

/-- The fixed `K = 1,500,000` specialization of the tail threshold. -/
theorem fixed_K_1500000_requires_upper_threshold
    {N t : ℝ} (hN : 0 < N)
    (hfrac0 : 0 < 1 - (1500000 : ℝ) / N)
    (hfrac1 : 1 - (1500000 : ℝ) / N < 1)
    (hcond : (t / 2) * Real.log (1500000 : ℝ) *
      (1 - (1500000 : ℝ) / N) > 1) :
    2 / Real.log (1500000 : ℝ) < t := by
  apply direct_tail_condition_requires_upper_threshold
    (K := (1500000 : ℝ)) (M := (1500000 : ℝ))
    (by norm_num) hN hfrac0 hfrac1 hcond
  · rfl
  · norm_num

/-- Positive natural `K,N` bounded by the unsigned 64-bit maximum obey the
exact `2 / log(ULONG_MAX)` threshold from the source. -/
theorem uint64_tail_condition_requires_upper_threshold
    {K N : ℕ} {t : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hKmax : K ≤ 2 ^ 64 - 1) (_hNmax : N ≤ 2 ^ 64 - 1)
    (hfrac0 : 0 < 1 - (K : ℝ) / (N : ℝ))
    (hfrac1 : 1 - (K : ℝ) / (N : ℝ) < 1)
    (hcond : (t / 2) * Real.log (K : ℝ) *
      (1 - (K : ℝ) / (N : ℝ)) > 1) :
    2 / Real.log ((2 ^ 64 - 1 : ℕ) : ℝ) < t := by
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hK)
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hKmax_real : (K : ℝ) ≤ ((2 ^ 64 - 1 : ℕ) : ℝ) := by
    exact_mod_cast hKmax
  apply direct_tail_condition_requires_upper_threshold
    (K := (K : ℝ)) (N := (N : ℝ))
    hKreal (by exact_mod_cast hN) hfrac0 hfrac1 hcond hKmax_real
  norm_num

theorem log_1500000_lt_two_hundred :
    Real.log (1500000 : ℝ) < 200 := by
  have htwo_exp : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog_two : Real.log (2 : ℝ) < 1 := by
    have h := Real.strictMonoOn_log (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show Real.exp 1 ∈ Set.Ioi 0 by
        change 0 < Real.exp 1
        exact Real.exp_pos _) htwo_exp
    simpa [Real.log_exp] using h
  have hpow : (1500000 : ℝ) < (2 : ℝ) ^ 21 := by norm_num
  have hlog_pow : Real.log (1500000 : ℝ) < Real.log ((2 : ℝ) ^ 21) :=
    Real.strictMonoOn_log (by norm_num) (show (0 : ℝ) < (2 : ℝ) ^ 21 by positivity) hpow
  rw [Real.log_pow] at hlog_pow
  have hlog_pow_bound : (21 : ℝ) * Real.log (2 : ℝ) < 21 := by
    nlinarith [hlog_two]
  have hlog_pow' : Real.log (1500000 : ℝ) < (21 : ℝ) * Real.log (2 : ℝ) := by
    simpa using hlog_pow
  nlinarith [hlog_pow', hlog_pow_bound]

/-- The fixed-`K` threshold is strictly above `0.01`, so this criterion cannot
certify a target with `t ≤ 0.01`. -/
theorem fixed_K_1500000_excludes_target_below_one_hundredth
    {N t : ℝ} (hN : 0 < N)
    (hfrac0 : 0 < 1 - (1500000 : ℝ) / N)
    (hfrac1 : 1 - (1500000 : ℝ) / N < 1)
    (hcond : (t / 2) * Real.log (1500000 : ℝ) *
      (1 - (1500000 : ℝ) / N) > 1) :
    (1 / 100 : ℝ) < t := by
  have hthreshold := fixed_K_1500000_requires_upper_threshold
    hN hfrac0 hfrac1 hcond
  have hlogpos : 0 < Real.log (1500000 : ℝ) := by norm_num [Real.log_pos]
  have hsmall : (1 / 100 : ℝ) < 2 / Real.log (1500000 : ℝ) := by
    apply (lt_div_iff₀ hlogpos).2
    have hlog := log_1500000_lt_two_hundred
    nlinarith
  exact lt_trans hsmall hthreshold

end MathlibPlus.Analysis.Claim1678
