import Mathlib

namespace MathlibPlus.NumberTheory.Claim17533

open scoped ArithmeticFunction.Moebius BigOperators
open ArithmeticFunction

/-!
The centered coordinate is made explicit: `R` is the product of the finite
prime set and `y d = log d - (log R)/2`.  The theorem keeps the finite
alternant identity separate from any analytic continuation or limiting claim.
-/

/-- Centering logarithmic divisor coordinates gives the finite Euler alternant
factorization. -/
theorem centered_alternant_factorization
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w : ℝ) :
    let R : ℕ := ∏ p ∈ P, p
    let y : ℕ → ℝ := fun d => Real.log d - Real.log R / 2
    (∑ d ∈ R.divisors, (μ d : ℝ) * Real.exp (-w * y d)) =
      ∏ p ∈ P, 2 * Real.sinh (w * Real.log p / 2) := by
  let R : ℕ := ∏ p ∈ P, p
  let y : ℕ → ℝ := fun d => Real.log d - Real.log R / 2
  let f : ArithmeticFunction ℝ :=
    ⟨fun n => if n = 0 then 0 else Real.exp (-w * Real.log n), by simp⟩
  have hf : f.IsMultiplicative := by
    refine ⟨by simp [f], ?_⟩
    intro m n hmn
    by_cases hm : m = 0
    · subst m
      have hn : n = 1 := (Nat.coprime_zero_left n).mp hmn
      subst n
      simp [f]
    by_cases hn : n = 0
    · subst n
      have hm' : m = 1 := (Nat.coprime_zero_right m).mp hmn
      subst m
      simp [f]
    simp only [f, ArithmeticFunction.coe_mk, Nat.cast_mul,
      if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]
    rw [Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
    rw [← Real.exp_add]
    congr 1
    ring
  have hpair : (P : Set ℕ).Pairwise (Function.onFun IsRelPrime id) := by
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
  have hR : Squarefree R := by
    dsimp [R]
    exact Finset.squarefree_prod_of_pairwise_isCoprime hpair
      (fun p hp =>
        (Nat.squarefree_and_prime_pow_iff_prime).mpr (hP p hp) |>.1)
  have hprod :
      (∏ p ∈ R.primeFactors, (1 - f p)) =
        ∑ d ∈ R.divisors, (μ d : ℝ) * f d := by
    exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      f hf hR
  have hprime : R.primeFactors = P := by
    exact Nat.primeFactors_prod hP
  rw [hprime] at hprod
  have hRlog : Real.log (R : ℝ) = ∑ p ∈ P, Real.log (p : ℝ) := by
    dsimp [R]
    rw [Nat.cast_prod]
    exact Real.log_prod (fun p hp => by exact_mod_cast (hP p hp).ne_zero)
  have hcenter :
      ∑ d ∈ R.divisors, (μ d : ℝ) * Real.exp (-w * y d) =
        Real.exp (w * Real.log R / 2) *
          (∑ d ∈ R.divisors, (μ d : ℝ) * f d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    dsimp [y, f]
    simp [hd0]
    rw [show -(w * (Real.log ↑d - Real.log ↑R / 2)) =
        w * Real.log ↑R / 2 + (-w * Real.log ↑d) by ring]
    rw [Real.exp_add]
    ring
  have hcommon :
      Real.exp (w * Real.log R / 2) =
        ∏ p ∈ P, Real.exp (w * Real.log (p : ℝ) / 2) := by
    rw [hRlog]
    rw [show w * (∑ p ∈ P, Real.log (p : ℝ)) / 2 =
        ∑ p ∈ P, (w * Real.log (p : ℝ) / 2) by
      rw [Finset.mul_sum, Finset.sum_div]]
    exact Real.exp_sum P (fun p => w * Real.log (p : ℝ) / 2)
  have hfactor (x : ℝ) :
      Real.exp x * (1 - Real.exp (-2 * x)) = 2 * Real.sinh x := by
    rw [Real.sinh_eq]
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring
  dsimp [R, y]
  rw [hcenter, ← hprod, hcommon, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  dsimp [f]
  simp only [if_neg (hP p hp).ne_zero]
  rw [show -w * Real.log (p : ℝ) =
      -2 * (w * Real.log (p : ℝ) / 2) by ring]
  exact hfactor (w * Real.log (p : ℝ) / 2)

end MathlibPlus.NumberTheory.Claim17533
