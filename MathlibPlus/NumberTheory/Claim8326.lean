import Mathlib

open scoped BigOperators
open Finset Nat

namespace MathlibPlus.NumberTheory

noncomputable section

/-- The positive-integer realization of `d ↦ d^(-v)` used in claim 8326.

For a complex parameter, this is defined by the exponential of the real
logarithm.  The value at zero is set to zero so that it is an arithmetic
function. -/
def claim8326DivisorPower (v : ℂ) (d : ℕ) : ℂ :=
  if d = 0 then 0 else Complex.exp (-v * Real.log d)

/-- Arithmetic-function packaging of `claim8326DivisorPower`. -/
def claim8326DivisorPowerAF (v : ℂ) : ArithmeticFunction ℂ :=
  ⟨claim8326DivisorPower v, by simp [claim8326DivisorPower]⟩

lemma claim8326_isMultiplicativeDivisorPowerAF (v : ℂ) :
    (claim8326DivisorPowerAF v).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [claim8326DivisorPowerAF, claim8326DivisorPower]
  · intro m n hmn
    by_cases hm : m = 0
    · simp [claim8326DivisorPowerAF, claim8326DivisorPower, hm]
    by_cases hn : n = 0
    · simp [claim8326DivisorPowerAF, claim8326DivisorPower, hn]
    change claim8326DivisorPower v (m * n) =
      claim8326DivisorPower v m * claim8326DivisorPower v n
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
    simp only [claim8326DivisorPower, hm, hn, hmn0, if_false]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [Nat.cast_mul, Real.log_mul hmR hnR]
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]

lemma claim8326_squarefreeDivisors_eq_radicalDivisors {k : ℕ} (hk : k ≠ 0) :
    k.divisors.filter Squarefree =
      (UniqueFactorizationMonoid.radical k).divisors := by
  ext d
  rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdk, hk0⟩, hsd⟩
    have hsub : d.primeFactors ⊆ k.primeFactors := Nat.primeFactors_mono hdk hk0
    have hsub' : d.primeFactors ⊆
        (UniqueFactorizationMonoid.radical k).primeFactors := by
      simpa only [Nat.primeFactors_radical] using hsub
    have hrad : UniqueFactorizationMonoid.radical d ∣
        UniqueFactorizationMonoid.radical k :=
      (Nat.radical_dvd_iff UniqueFactorizationMonoid.radical_ne_zero).2 hsub'
    have hd_rad : UniqueFactorizationMonoid.radical d = d := by
      rw [Nat.radical_eq_prod_primeFactors, Nat.prod_primeFactors_of_squarefree hsd]
    exact ⟨by rwa [hd_rad] at hrad, UniqueFactorizationMonoid.radical_ne_zero⟩
  · rintro ⟨hdr, hr0⟩
    have hdk : d ∣ k := hdr.trans UniqueFactorizationMonoid.radical_dvd_self
    exact ⟨⟨hdk, hk⟩,
      (UniqueFactorizationMonoid.squarefree_radical).squarefree_of_dvd hdr⟩

lemma claim8326_moebiusSum_eq_radicalSum {R : Type*} [CommRing R]
    {f : ℕ → R} {k : ℕ} (hk : k ≠ 0) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : R) * f d) =
      ∑ d ∈ (UniqueFactorizationMonoid.radical k).divisors,
        (ArithmeticFunction.moebius d : R) * f d := by
  have hfilter := claim8326_squarefreeDivisors_eq_radicalDivisors hk
  rw [← hfilter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsd : Squarefree d
  · simp [hsd]
  · simp [hsd, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsd]

lemma claim8326_prodSub_eq_moebiusSum {R : Type*} [CommRing R]
    (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {k : ℕ} (hk : k ≠ 0) :
    (∏ p ∈ k.primeFactors, (1 - f p)) =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : R) * f d := by
  calc
    (∏ p ∈ k.primeFactors, (1 - f p)) =
        ∏ p ∈ (UniqueFactorizationMonoid.radical k).primeFactors, (1 - f p) := by
          rw [Nat.primeFactors_radical]
    _ = ∑ d ∈ (UniqueFactorizationMonoid.radical k).divisors,
        (ArithmeticFunction.moebius d : R) * f d :=
      ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree f hf
        UniqueFactorizationMonoid.squarefree_radical
    _ = ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : R) * f d :=
      (claim8326_moebiusSum_eq_radicalSum (R := R) (f := f) hk).symm

/-- The generalized Jordan divisor coefficient from claim 8326. -/
def claim8326G (v : ℂ) (k : ℕ) : ℂ :=
  ∏ p ∈ k.primeFactors, (1 - claim8326DivisorPower v p)

/-- `g_v(k) = ∏_{p ∣ k}(1-p^(-v)) = ∑_{d ∣ k} μ(d)d^(-v)` for `k ≥ 1`.

The complex power of a positive integer is represented by
`exp (-v * log d)`, which agrees with the principal power on the positive
real axis. -/
theorem claim8326G_eq_moebiusSum {v : ℂ} {k : ℕ} (hk : 0 < k) :
    claim8326G v k =
      ∑ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℂ) * claim8326DivisorPower v d := by
  unfold claim8326G
  exact claim8326_prodSub_eq_moebiusSum
    (claim8326DivisorPowerAF v)
    (claim8326_isMultiplicativeDivisorPowerAF v)
    (Nat.ne_of_gt hk)

end

end MathlibPlus.NumberTheory
