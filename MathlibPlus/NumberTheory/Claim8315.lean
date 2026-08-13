import Mathlib

namespace MathlibPlus.NumberTheory.Claim8315

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction

/-- The exact finite Cauchy--Schwarz step in the gcd-layer estimate. -/
theorem gcd_layer_energy_cauchy {E : ℕ → ℕ → ℕ → ℂ}
    {g M a c : ℕ} (hg : Squarefree g) :
    ‖∑ d ∈ g.divisors,
        ((μ d : ℂ) / (d : ℂ)) * E M (a * d) c‖ ^ 2 ≤
      (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) *
        ∑ d ∈ g.divisors, ‖E M (a * d) c‖ ^ 2 := by
  have hg0 : g ≠ 0 := hg.ne_zero
  let s : Finset ℕ := g.divisors
  have hnorm :
      ‖∑ d ∈ s, ((μ d : ℂ) / (d : ℂ)) * E M (a * d) c‖ ≤
        ∑ d ∈ s, (|μ d| : ℝ) * (d : ℝ)⁻¹ * ‖E M (a * d) c‖ := by
    calc
      ‖∑ d ∈ s, ((μ d : ℂ) / (d : ℂ)) * E M (a * d) c‖ ≤
          ∑ d ∈ s, ‖((μ d : ℂ) / (d : ℂ)) * E M (a * d) c‖ :=
        norm_sum_le _ _
      _ = ∑ d ∈ s, (|μ d| : ℝ) * (d : ℝ)⁻¹ * ‖E M (a * d) c‖ := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdp : 0 < d := Nat.pos_of_mem_divisors hd
        have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdp)
        simp [div_eq_mul_inv, Complex.norm_intCast]
  have hsq :
      (∑ d ∈ s, (|μ d| : ℝ) * (d : ℝ)⁻¹ * ‖E M (a * d) c‖) ^ 2 ≤
        (∑ d ∈ s, ((|μ d| : ℝ) * (d : ℝ)⁻¹) ^ 2) *
          ∑ d ∈ s, ‖E M (a * d) c‖ ^ 2 := by
    simpa [mul_assoc] using
      (Finset.sum_mul_sq_le_sq_mul_sq s
        (fun d => (|μ d| : ℝ) * (d : ℝ)⁻¹)
        (fun d => ‖E M (a * d) c‖))
  have hcoeff :
      (∑ d ∈ s, ((|μ d| : ℝ) * (d : ℝ)⁻¹) ^ 2) ≤
        ∑ d ∈ s, ((d : ℝ)⁻¹) ^ 2 := by
    apply Finset.sum_le_sum
    intro d hd
    have hdp : 0 < d := Nat.pos_of_mem_divisors hd
    have hm : (|μ d| : ℝ) ≤ 1 := by
      exact_mod_cast (abs_moebius_le_one (n := d))
    have hi : 0 ≤ (d : ℝ)⁻¹ := by positivity
    exact (sq_le_sq₀ (mul_nonneg (by positivity) hi) hi).2
      (by simpa using mul_le_mul_of_nonneg_right hm hi)
  have hnonneg : 0 ≤ ∑ d ∈ s, ‖E M (a * d) c‖ ^ 2 := by positivity
  calc
    ‖∑ d ∈ g.divisors, ((μ d : ℂ) / (d : ℂ)) * E M (a * d) c‖ ^ 2 ≤
        (∑ d ∈ s, (|μ d| : ℝ) * (d : ℝ)⁻¹ * ‖E M (a * d) c‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (Finset.sum_nonneg fun d _ => mul_nonneg (by positivity) (by positivity))).2
        (by simpa [s] using hnorm)
    _ ≤ (∑ d ∈ s, ((|μ d| : ℝ) * (d : ℝ)⁻¹) ^ 2) *
          ∑ d ∈ s, ‖E M (a * d) c‖ ^ 2 := hsq
    _ ≤ (∑ d ∈ s, ((d : ℝ)⁻¹) ^ 2) *
          ∑ d ∈ s, ‖E M (a * d) c‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff hnonneg

/-- For a squarefree modulus, the divisor-square sum is exactly the finite
Euler product over its prime support. -/
theorem gcd_layer_divisor_product {g : ℕ} (hg : Squarefree g) :
    (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) =
      ∏ p ∈ g.primeFactors, (1 + ((p : ℝ)⁻¹) ^ 2) := by
  let f : ArithmeticFunction ℝ :=
    ⟨fun n => if n = 0 then 0 else (n : ℝ)⁻¹ ^ 2, by simp⟩
  have hf : f.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f]
    · intro m n hmn
      by_cases hm : m = 0
      · simp [f, hm]
      by_cases hn : n = 0
      · simp [f, hn]
      dsimp [f]
      simp only [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
      rw [Nat.cast_mul, mul_inv_rev]
      ring
  have h := hf.prodPrimeFactors_one_add_of_squarefree hg
  calc
    (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) =
        ∑ d ∈ g.divisors, f d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdp : 0 < d := Nat.pos_of_mem_divisors hd
      simp [f, Nat.ne_of_gt hdp]
    _ = ∏ p ∈ g.primeFactors, (1 + f p) := h.symm
    _ = ∏ p ∈ g.primeFactors, (1 + ((p : ℝ)⁻¹) ^ 2) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpp : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
      simp [f, hpp.ne']

end MathlibPlus.NumberTheory.Claim8315
