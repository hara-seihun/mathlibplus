import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory.Claim40564

/--
The exact two-coordinate transition arithmetic from admitted claim 40564.
The hypotheses expose the part of "admissible even prefix" used by the
transition: the current remainder is `y / d`, the current last prime is in
its lower state band, and appending the ordered primes `q,r` satisfies the
cubic stopping inequality `d*q*r^3 < y`.
-/
theorem twoCoordinateStateAndTransition_claim40564
    (d y p q r : ℕ)
    (hd : 0 < d)
    (hdy : d < y)
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hr : Nat.Prime r)
    (hqp : q < p)
    (hrq : r < q)
    (hstop : d * q * r ^ 3 < y)
    (hα : Real.log (p : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) < (1 : ℝ) / 2) :
    let T : ℝ := Real.log ((y : ℝ) / (d : ℝ))
    let α : ℝ := Real.log (p : ℝ) / T
    let x : ℝ := Real.log (q : ℝ) / T
    let z : ℝ := Real.log (r : ℝ) / T
    let T' : ℝ := Real.log ((y : ℝ) / ((d * q * r : ℕ) : ℝ))
    let α' : ℝ := Real.log (r : ℝ) / T'
    0 < α ∧ α < (1 : ℝ) / 2 ∧
      0 < x ∧ x < α ∧
      0 < z ∧ z < min x ((1 - x) / 3) ∧
      T' = T * (1 - x - z) ∧
      α' = z / (1 - x - z) := by
  dsimp
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast hd
  have hdyR : (d : ℝ) < (y : ℝ) := by
    exact_mod_cast hdy
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (Nat.Prime.pos hq)
  have hrR : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (Nat.Prime.pos hr)
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.Prime.pos hp)
  have hq1R : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq.one_lt
  have hr1R : (1 : ℝ) < (r : ℝ) := by
    exact_mod_cast hr.one_lt
  have hp1R : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hYd : (1 : ℝ) < (y : ℝ) / (d : ℝ) := by
    apply (lt_div_iff₀ hdR).2
    simpa using hdyR
  have hT : 0 < Real.log ((y : ℝ) / (d : ℝ)) := Real.log_pos hYd
  have hTne : Real.log ((y : ℝ) / (d : ℝ)) ≠ 0 := ne_of_gt hT
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1R
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1R
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hr1R
  have hqpR : (q : ℝ) < (p : ℝ) := by
    exact_mod_cast hqp
  have hlogqp : Real.log (q : ℝ) < Real.log (p : ℝ) := by
    exact Real.strictMonoOn_log hqR hpR hqpR
  have hrqR : (r : ℝ) < (q : ℝ) := by
    exact_mod_cast hrq
  have hlogrq : Real.log (r : ℝ) < Real.log (q : ℝ) := by
    exact Real.strictMonoOn_log hrR hqR hrqR
  have hstopR : ((d * q * r ^ 3 : ℕ) : ℝ) < (y : ℝ) := by
    exact_mod_cast hstop
  have hprodNat : 0 < d * q * r ^ 3 := by
    exact Nat.mul_pos (Nat.mul_pos hd (Nat.Prime.pos hq))
      (pow_pos (Nat.Prime.pos hr) _)
  have hprodR : (0 : ℝ) < ((d * q * r ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hprodNat
  have hyR : (0 : ℝ) < (y : ℝ) := lt_trans hdR hdyR
  have hlogstop : Real.log ((d * q * r ^ 3 : ℕ) : ℝ) < Real.log (y : ℝ) := by
    exact Real.strictMonoOn_log hprodR hyR hstopR
  have hlogprod :
      Real.log ((d * q * r ^ 3 : ℕ) : ℝ) =
        Real.log (d : ℝ) + Real.log (q : ℝ) + 3 * Real.log (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (ne_of_gt (mul_pos hdR hqR)) (by positivity)]
    rw [Real.log_pow]
    rw [Real.log_mul (ne_of_gt hdR) (ne_of_gt hqR)]
    ring
  have hlogstop' :
      Real.log (d : ℝ) + Real.log (q : ℝ) + 3 * Real.log (r : ℝ) <
        Real.log (y : ℝ) := by
    rw [← hlogprod]
    exact hlogstop
  have hlogdiv :
      Real.log ((y : ℝ) / (d : ℝ)) = Real.log (y : ℝ) - Real.log (d : ℝ) := by
    rw [Real.log_div (by positivity) (by positivity)]
  have hlogdiv_child :
      Real.log ((y : ℝ) / ((d * q * r : ℕ) : ℝ)) =
        Real.log (y : ℝ) - Real.log (d : ℝ) - Real.log (q : ℝ) - Real.log (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_mul (ne_of_gt (mul_pos hdR hqR)) (ne_of_gt hrR)]
    rw [Real.log_mul (ne_of_gt hdR) (ne_of_gt hqR)]
    ring
  have hsum :
      Real.log (q : ℝ) + 3 * Real.log (r : ℝ) <
        Real.log ((y : ℝ) / (d : ℝ)) := by
    rw [hlogdiv]
    linarith
  have hsum1 :
      Real.log (q : ℝ) + Real.log (r : ℝ) <
        Real.log ((y : ℝ) / (d : ℝ)) := by
    linarith
  have hscaled3 :
      (Real.log (q : ℝ) + 3 * Real.log (r : ℝ)) /
          Real.log ((y : ℝ) / (d : ℝ)) < 1 := by
    apply (div_lt_iff₀ hT).2
    linarith
  have hscaled1 :
      (Real.log (q : ℝ) + Real.log (r : ℝ)) /
          Real.log ((y : ℝ) / (d : ℝ)) < 1 := by
    apply (div_lt_iff₀ hT).2
    linarith
  have hscaled3' :
      Real.log (q : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) +
          3 * (Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ))) < 1 := by
    have heq :
        (Real.log (q : ℝ) + 3 * Real.log (r : ℝ)) /
            Real.log ((y : ℝ) / (d : ℝ)) =
          Real.log (q : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) +
            3 * (Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ))) := by
      field_simp [hTne]
    rw [← heq]
    exact hscaled3
  have hscaled1' :
      Real.log (q : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) +
          Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) < 1 := by
    have heq :
        (Real.log (q : ℝ) + Real.log (r : ℝ)) /
            Real.log ((y : ℝ) / (d : ℝ)) =
          Real.log (q : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) +
            Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) := by
      field_simp [hTne]
    rw [← heq]
    exact hscaled1
  have hden :
      0 < 1 - Real.log (q : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) -
          Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) := by
    linarith
  have hTprime :
      Real.log ((y : ℝ) / ((d * q * r : ℕ) : ℝ)) =
        Real.log ((y : ℝ) / (d : ℝ)) *
          (1 - Real.log (q : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) -
            Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ))) := by
    field_simp [hTne]
    rw [hlogdiv_child, hlogdiv]
  have hαprime :
      Real.log (r : ℝ) / Real.log ((y : ℝ) / ((d * q * r : ℕ) : ℝ)) =
        (Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ))) /
          (1 - Real.log (q : ℝ) / Real.log ((y : ℝ) / (d : ℝ)) -
            Real.log (r : ℝ) / Real.log ((y : ℝ) / (d : ℝ))) := by
    rw [hTprime]
    field_simp [hTne, ne_of_gt hden]
  refine ⟨div_pos hlogp hT, hα, div_pos hlogq hT, ?_,
    div_pos hlogr hT, ?_, hTprime, hαprime⟩
  · exact (div_lt_div_iff_of_pos_right hT).2 hlogqp
  · apply lt_min
    · exact (div_lt_div_iff_of_pos_right hT).2 hlogrq
    · linarith

end MathlibPlus.NumberTheory.Claim40564
