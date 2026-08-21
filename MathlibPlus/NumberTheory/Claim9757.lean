import Mathlib

namespace MathlibPlus.NumberTheory.Claim9757

open ArithmeticFunction
open UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

/-- The reciprocal-of-index arithmetic function, with the standard zero value at `0`. -/
noncomputable def reciprocalIndexQ : ArithmeticFunction ℚ where
  toFun n := if n = 0 then 0 else (n : ℚ)⁻¹
  map_zero' := by simp

@[simp] theorem reciprocalIndexQ_apply (n : ℕ) :
    reciprocalIndexQ n = if n = 0 then 0 else (n : ℚ)⁻¹ := rfl

theorem reciprocalIndexQ_isMultiplicative : reciprocalIndexQ.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · simp [reciprocalIndexQ]
  · intro m n hm hn hcop
    have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    simp only [reciprocalIndexQ_apply, if_neg hm, if_neg hn, if_neg hmn]
    push_cast
    field_simp

noncomputable def fareyConvolutionCoeff : ArithmeticFunction ℚ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℚ) * reciprocalIndexQ

theorem fareyConvolutionCoeff_isMultiplicative :
    fareyConvolutionCoeff.IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    reciprocalIndexQ_isMultiplicative

theorem fareyConvolutionCoeff_eq_source_sum (n : ℕ) :
    fareyConvolutionCoeff n =
      if n = 0 then 0 else
        (∑ d ∈ n.divisors, (d : ℚ) * (ArithmeticFunction.moebius d : ℚ)) / n := by
  by_cases hn : n = 0
  · subst n
    simp [fareyConvolutionCoeff, reciprocalIndexQ]
  · unfold fareyConvolutionCoeff
    rw [ArithmeticFunction.mul_apply]
    have hswap :
        (∑ x ∈ n.divisorsAntidiagonal,
            (ArithmeticFunction.moebius x.1 : ℚ) * reciprocalIndexQ x.2) =
          ∑ x ∈ n.divisorsAntidiagonal,
            reciprocalIndexQ x.1 * (ArithmeticFunction.moebius x.2 : ℚ) := by
      rw [← Nat.map_swap_divisorsAntidiagonal]
      rw [Finset.sum_map]
      simp [mul_comm]
    simp only [if_neg hn]
    calc
      (∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℚ) * reciprocalIndexQ x.2) =
          ∑ x ∈ n.divisorsAntidiagonal,
            reciprocalIndexQ x.1 * (ArithmeticFunction.moebius x.2 : ℚ) := hswap
      _ = ∑ d ∈ n.divisors,
            reciprocalIndexQ (n / d) * (ArithmeticFunction.moebius d : ℚ) := by
          exact Nat.sum_divisorsAntidiagonal' (f := fun x y =>
            reciprocalIndexQ x * (ArithmeticFunction.moebius y : ℚ))
      _ = ∑ d ∈ n.divisors,
            ((d : ℚ) * (ArithmeticFunction.moebius d : ℚ)) * (n : ℚ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
        have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
        have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
        simp only [reciprocalIndexQ_apply, if_neg hqpos.ne']
        have hcast : ((n / d : ℕ) : ℚ) * (d : ℚ) = (n : ℚ) := by
          rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
        field_simp
        linear_combination -((ArithmeticFunction.moebius d : ℚ)) * hcast
      _ = (∑ d ∈ n.divisors, (d : ℚ) * (ArithmeticFunction.moebius d : ℚ)) *
            (n : ℚ)⁻¹ := by
        exact (Finset.sum_mul n.divisors
          (fun d => (d : ℚ) * (ArithmeticFunction.moebius d : ℚ)) (n : ℚ)⁻¹).symm
      _ = (∑ d ∈ n.divisors, (d : ℚ) * (ArithmeticFunction.moebius d : ℚ)) / n := by
        rw [div_eq_mul_inv]

lemma weightedMobius_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ∑ d ∈ (p ^ a).divisors, (d : ℚ) *
      (ArithmeticFunction.moebius d : ℚ) = 1 - p := by
  rw [Nat.sum_divisors_prime_pow hp]
  induction a with
  | zero => omega
  | succ a ih =>
      by_cases ha0 : a = 0
      · subst a
        norm_num [Finset.sum_range_succ,
          ArithmeticFunction.moebius_apply_one,
          ArithmeticFunction.moebius_apply_prime hp]
        ring
      · have ha_pos : 1 ≤ a := by omega
        have ih' := ih ha_pos
        rw [show a + 1 + 1 = (a + 1) + 1 by omega,
          Finset.sum_range_succ]
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [ha0]
        simpa only [Nat.cast_pow] using ih'

theorem fareyConvolutionCoeff_eq_divisor_sum (n : ℕ) :
    fareyConvolutionCoeff n =
      ((n : ℚ)⁻¹) * ∑ d ∈ n.divisors, (d : ℚ) *
        (ArithmeticFunction.moebius d : ℚ) := by
  rw [fareyConvolutionCoeff_eq_source_sum]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn, div_eq_mul_inv]
    ring

theorem fareyConvolutionCoeff_prime_pow
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    fareyConvolutionCoeff (p ^ k) = -(p - 1 : ℚ) / (p ^ k : ℚ) := by
  rw [fareyConvolutionCoeff_eq_source_sum]
  · rw [Nat.sum_divisors_prime_pow hp]
    have hterm : ∀ j : ℕ,
        (p ^ j : ℚ) * (ArithmeticFunction.moebius (p ^ j) : ℚ) =
          if j = 0 then 1 else if j = 1 then -(p : ℚ) else 0 := by
      intro j
      by_cases hj0 : j = 0
      · simp [hj0]
      by_cases hj1 : j = 1
      · rw [hj1]
        simp [ArithmeticFunction.moebius_apply_prime hp]
      · have hm : (ArithmeticFunction.moebius (p ^ j) : ℚ) = 0 := by
          simpa [hj1] using congrArg (fun z : ℤ => (z : ℚ))
            (ArithmeticFunction.moebius_apply_prime_pow (p := p) (k := j) hp hj0)
        rw [hm]
        simp [hj0, hj1]
    simp only [pow_ne_zero k hp.ne_zero, if_false, Nat.cast_pow]
    simp_rw [hterm]
    have hk1 : 1 ≤ k := hk
    let s : Finset ℕ := Finset.range (k + 1)
    have hsum : Finset.sum s (fun x =>
        if x = 0 then 1 else if x = 1 then -(p : ℚ) else 0) = 1 - p := by
      calc
        Finset.sum s (fun x =>
            if x = 0 then 1 else if x = 1 then -(p : ℚ) else 0) =
            Finset.sum s (fun x =>
              (if x = 0 then 1 else 0) + (if x = 1 then -(p : ℚ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [h0, h1]
        _ = (if 0 ∈ s then 1 else 0) +
            (if 1 ∈ s then -(p : ℚ) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        _ = 1 - p := by
          dsimp [s]
          simp only [Finset.mem_range]
          have hk0 : 0 < k := by omega
          simp [hk0]
          ring
    rw [show Finset.sum (Finset.range (k + 1)) (fun x =>
        if x = 0 then 1 else if x = 1 then -(p : ℚ) else 0) = 1 - p by simpa [s] using hsum]
    field_simp
    ring

theorem fareyConvolutionCoeff_radical_formula (n : ℕ) :
    fareyConvolutionCoeff n =
      (ArithmeticFunction.moebius (radical n) : ℚ) *
        (Nat.totient (radical n) : ℚ) / n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero =>
      simp [fareyConvolutionCoeff, reciprocalIndexQ]
  | one =>
      change ((ArithmeticFunction.moebius : ArithmeticFunction ℚ) * reciprocalIndexQ) 1 = _
      rw [ArithmeticFunction.mul_apply]
      simp [reciprocalIndexQ]
  | prime_pow p k hp hk =>
      rw [fareyConvolutionCoeff_prime_pow hp hk]
      rw [UniqueFactorizationMonoid.radical_pow_of_prime (Nat.prime_iff.mp hp) hk.ne']
      simp [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
      rw [Nat.cast_sub hp.one_le]
      ring
  | coprime a b ha hb hab hfa hfb =>
      have hrab : Nat.Coprime (radical a) (radical b) :=
        (hab.coprime_dvd_left radical_dvd_self).coprime_dvd_right radical_dvd_self
      rw [fareyConvolutionCoeff_isMultiplicative.map_mul_of_coprime (by simpa using hab)]
      rw [hfa, hfb, UniqueFactorizationMonoid.radical_mul
        (Nat.coprime_iff_isRelPrime.mp hab)]
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hrab]
      rw [Nat.totient_mul hrab]
      push_cast
      ring

end MathlibPlus.NumberTheory.Claim9757
