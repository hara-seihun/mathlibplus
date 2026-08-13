import Mathlib

open scoped ArithmeticFunction.Moebius

namespace MathlibPlus.NumberTheory.Claim9753

/-- The Möbius-over-index arithmetic function has reciprocal `1/n` for Dirichlet
convolution; consequently the associated divisor transform is inverted by the
factor `d/n`. -/
theorem dirichletInverse_mu_div_index_claim9753
    (z e : ℕ → ℚ)
    (hze : ∀ n : ℕ, 0 < n →
      z n = ∑ d ∈ n.divisors,
        (μ d : ℚ) / (d : ℚ) * e (n / d)) :
    ∀ n : ℕ, 0 < n →
      e n = ∑ d ∈ n.divisors, ((d : ℚ) / (n : ℚ)) * z d := by
  let a : ArithmeticFunction ℚ :=
    ⟨fun n => (μ n : ℚ) / (n : ℚ), by simp⟩
  let b : ArithmeticFunction ℚ :=
    ⟨fun n => 1 / (n : ℚ), by simp⟩
  have hab : a * b = 1 := by
    have hconv : ∀ {n : ℕ}, 0 < n →
        (∑ d ∈ n.divisors,
          (μ d : ℚ) / (d : ℚ) * (1 / (n / d : ℚ))) =
          if n = 1 then 1 else 0 := by
      intro n hn
      have hsum :
          (∑ d ∈ n.divisors, (μ d : ℚ)) = if n = 1 then 1 else 0 := by
        have h := congrArg (fun f : ArithmeticFunction ℚ => f n)
          (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℚ))
        rw [ArithmeticFunction.coe_mul_zeta_apply] at h
        simpa [ArithmeticFunction.one_apply] using h
      have hfactor : ∀ d ∈ n.divisors,
          (μ d : ℚ) / (d : ℚ) * (1 / (n / d : ℚ)) =
            (μ d : ℚ) / (n : ℚ) := by
        intro d hd
        have hddiv : d ∣ n := Nat.dvd_of_mem_divisors hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddiv hn
        have hle : d ≤ n := Nat.le_of_dvd hn hddiv
        have hndpos : 0 < n / d := Nat.div_pos hle hdpos
        have hprod : d * (n / d) = n := Nat.mul_div_cancel' hddiv
        field_simp
      calc
        (∑ d ∈ n.divisors,
            (μ d : ℚ) / (d : ℚ) * (1 / (n / d : ℚ))) =
            ∑ d ∈ n.divisors, (μ d : ℚ) / (n : ℚ) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact hfactor d hd
        _ = (∑ d ∈ n.divisors, (μ d : ℚ)) / (n : ℚ) := by
          rw [Finset.sum_div]
        _ = (if n = 1 then 1 else 0) / (n : ℚ) := by rw [hsum]
        _ = if n = 1 then 1 else 0 := by
          by_cases h : n = 1 <;> simp [h]
    ext n
    cases n with
    | zero => simp [a, b]
    | succ n =>
      rw [ArithmeticFunction.mul_apply]
      rw [Nat.sum_divisorsAntidiagonal (fun i j => a i * b j)]
      calc
        (∑ d ∈ (n + 1).divisors, a d * b ((n + 1) / d)) =
            ∑ d ∈ (n + 1).divisors,
              (μ d : ℚ) / (d : ℚ) *
                (1 / (((n + 1 : ℕ) : ℚ) / (d : ℚ))) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hddiv : d ∣ n + 1 := Nat.dvd_of_mem_divisors hd
          have hcast : (((n + 1) / d : ℕ) : ℚ) =
              ((n + 1 : ℕ) : ℚ) / (d : ℚ) :=
            Nat.cast_div hddiv
              (by exact_mod_cast
                (Nat.ne_of_gt
                  (Nat.pos_of_dvd_of_pos hddiv (Nat.succ_pos n))))
          simp [a, b, hcast, div_eq_mul_inv]
        _ = if n + 1 = 1 then 1 else 0 := by
          exact hconv (Nat.succ_pos n)
        _ = (1 : ArithmeticFunction ℚ) (n + 1) := by
          simp [ArithmeticFunction.one_apply]
  let Z : ArithmeticFunction ℚ :=
    ⟨fun n => if n = 0 then 0 else z n, by simp⟩
  let E : ArithmeticFunction ℚ :=
    ⟨fun n => if n = 0 then 0 else e n, by simp⟩
  have hZE : Z = a * E := by
    ext n
    cases n with
    | zero => simp [Z, E]
    | succ n =>
      rw [ArithmeticFunction.mul_apply]
      rw [Nat.sum_divisorsAntidiagonal (fun i j => a i * E j)]
      calc
        Z (n + 1) = z (n + 1) := by simp [Z]
        _ = ∑ d ∈ (n + 1).divisors,
              (μ d : ℚ) / (d : ℚ) * e ((n + 1) / d) :=
          hze (n + 1) (Nat.succ_pos n)
        _ = ∑ d ∈ (n + 1).divisors, a d * E ((n + 1) / d) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hddiv : d ∣ n + 1 := Nat.dvd_of_mem_divisors hd
          have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddiv (Nat.succ_pos n)
          have hqpos : 0 < (n + 1) / d :=
            Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hddiv) hdpos
          simp [a, E, hqpos.ne']
  have hba : b * a = 1 := by
    rw [mul_comm]
    exact hab
  have hE : b * Z = E := by
    calc
      b * Z = b * (a * E) := by rw [hZE]
      _ = (b * a) * E := by rw [mul_assoc]
      _ = E := by rw [hba, one_mul]
  intro n hn
  have hpoint := congrArg (fun f : ArithmeticFunction ℚ => f n) hE
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun i j => b i * Z j)] at hpoint
  have hpoint' :
      (∑ d ∈ n.divisors, (1 / (((n / d : ℕ) : ℚ))) * z d) = e n := by
    calc
      (∑ d ∈ n.divisors,
          (1 / (((n / d : ℕ) : ℚ))) * z d) =
          ∑ d ∈ n.divisors, b (n / d) * Z d := by
        apply Finset.sum_congr rfl
        intro d hd
        have hddiv : d ∣ n := Nat.dvd_of_mem_divisors hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddiv hn
        simp [b, Z, hdpos.ne']
      _ = e n := by simpa [E, hn.ne'] using hpoint
  calc
    e n = ∑ d ∈ n.divisors, (1 / (((n / d : ℕ) : ℚ))) * z d := hpoint'.symm
    _ = ∑ d ∈ n.divisors, ((d : ℚ) / (n : ℚ)) * z d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hddiv : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddiv hn
      have hcast : (((n / d : ℕ) : ℚ)) = (n : ℚ) / (d : ℚ) :=
        Nat.cast_div hddiv (by exact_mod_cast hdpos.ne')
      rw [hcast]
      field_simp

end MathlibPlus.NumberTheory.Claim9753
