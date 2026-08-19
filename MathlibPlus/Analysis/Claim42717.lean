import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.NatDivisors
import MathlibPlus.NumberTheory.Claim9757
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

set_option linter.style.header false

namespace MathlibPlus.Analysis.Claim42717

open UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

def fareyGcdKernel (d e : ℕ) : ℚ :=
  (Nat.gcd d e : ℚ) ^ 2 / ((d : ℚ) * (e : ℚ))

theorem fareyGcdKernel_symmetric (d e : ℕ) :
    fareyGcdKernel d e = fareyGcdKernel e d := by
  simp [fareyGcdKernel, Nat.gcd_comm, mul_comm]

private def finiteKernelPairing
    (s t : Finset ℕ) (K : ℕ → ℕ → ℚ)
    (u v : ℕ → ℚ) : ℚ :=
  ∑ i ∈ s, ∑ j ∈ t, u i * v j * K i j

noncomputable def mobiusLayerInner (m n : ℕ) : ℚ :=
  finiteKernelPairing m.divisors n.divisors fareyGcdKernel
    (fun d => (ArithmeticFunction.moebius (m / d) : ℚ))
    (fun e => (ArithmeticFunction.moebius (n / e) : ℚ))

theorem fareyGcdKernel_mul_of_crossCoprime
    {d₁ d₂ e₁ e₂ : ℕ}
    (d₁CoprimeD₂ : d₁.Coprime d₂)
    (e₁CoprimeE₂ : e₁.Coprime e₂)
    (d₂CoprimeE₁ : d₂.Coprime e₁)
    (d₁CoprimeE₂ : d₁.Coprime e₂) :
    fareyGcdKernel (d₁ * d₂) (e₁ * e₂)
      = fareyGcdKernel d₁ e₁ * fareyGcdKernel d₂ e₂ := by
  have gcdFactor :
      Nat.gcd (d₁ * d₂) (e₁ * e₂)
        = Nat.gcd d₁ e₁ * Nat.gcd d₂ e₂ := by
    rw [e₁CoprimeE₂.gcd_mul]
    have first :
        Nat.gcd (d₁ * d₂) e₁ = Nat.gcd d₁ e₁ := by
      rw [Nat.gcd_comm, d₁CoprimeD₂.gcd_mul]
      rw [d₂CoprimeE₁.symm.gcd_eq_one, mul_one, Nat.gcd_comm]
    have second :
        Nat.gcd (d₁ * d₂) e₂ = Nat.gcd d₂ e₂ := by
      rw [Nat.gcd_comm, d₁CoprimeD₂.gcd_mul]
      rw [d₁CoprimeE₂.symm.gcd_eq_one, one_mul, Nat.gcd_comm]
    rw [first, second]
  unfold fareyGcdKernel
  rw [gcdFactor]
  push_cast
  ring

theorem fareyGcdKernel_mul_right
    {d q : ℕ} (dPositive : 0 < d) (qPositive : 0 < q) :
    fareyGcdKernel d (d * q) = (q : ℚ)⁻¹ := by
  unfold fareyGcdKernel
  rw [Nat.gcd_eq_left_iff_dvd.mpr (dvd_mul_right d q)]
  push_cast
  field_simp

theorem fareyGcdKernel_primePowers_of_le
    {p i j : ℕ} (pPositive : 0 < p) (ij : i ≤ j) :
    fareyGcdKernel (p ^ i) (p ^ j)
      = (p ^ (j - i) : ℚ)⁻¹ := by
  have factorization : p ^ j = p ^ i * p ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_of_le ij]
  rw [factorization]
  simpa using
    (fareyGcdKernel_mul_right (pow_pos pPositive i)
      (pow_pos pPositive (j - i)))

/-- On every prime-power chain, the Farey gcd kernel is the geometric Toeplitz kernel. -/
theorem fareyGcdKernel_primePowers (p i j : ℕ) (pPositive : 0 < p) :
    fareyGcdKernel (p ^ i) (p ^ j) =
      (p ^ Nat.dist i j : ℚ)⁻¹ := by
  by_cases hij : i ≤ j
  · rw [fareyGcdKernel_primePowers_of_le pPositive hij]
    simp [Nat.dist_eq_sub_of_le hij]
  · have hji : j ≤ i := Nat.le_of_not_ge hij
    rw [fareyGcdKernel_symmetric]
    rw [fareyGcdKernel_primePowers_of_le pPositive hji]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji]

theorem moebiusPrimePower_weightedRange
    {p t : ℕ} (pPrime : p.Prime) (f : ℕ → ℚ) :
    (∑ x ∈ Finset.range (t.succ + 1),
      (ArithmeticFunction.moebius (p ^ t.succ / p ^ x) : ℚ) * f x)
      =
    -f t + f t.succ := by
  let coeff : ℕ → ℚ :=
    fun x => (ArithmeticFunction.moebius (p ^ t.succ / p ^ x) : ℚ)
  have coeffEarly {x : ℕ} (xEarly : x < t) :
      coeff x = 0 := by
    have xLe : x ≤ t.succ := by omega
    have exponentNonzero : t.succ - x ≠ 0 := by omega
    have exponentNotOne : t.succ - x ≠ 1 := by omega
    unfold coeff
    rw [Nat.pow_div xLe pPrime.pos,
      ArithmeticFunction.moebius_apply_prime_pow pPrime exponentNonzero,
      if_neg exponentNotOne]
    norm_num
  have coeffAtT : coeff t = -1 := by
    unfold coeff
    rw [Nat.pow_div (by omega) pPrime.pos]
    simp [ArithmeticFunction.moebius_apply_prime pPrime]
  have coeffAtSucc : coeff t.succ = 1 := by
    unfold coeff
    rw [Nat.pow_div (by omega) pPrime.pos]
    simp
  change (∑ x ∈ Finset.range (t.succ + 1), coeff x * f x)
    = -f t + f t.succ
  rw [show t.succ + 1 = (t + 1) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have earlySum :
      ∑ x ∈ Finset.range t, coeff x * f x = 0 := by
    apply Finset.sum_eq_zero
    intro x xMem
    rw [coeffEarly (Finset.mem_range.mp xMem), zero_mul]
  rw [earlySum, zero_add, coeffAtT, coeffAtSucc]
  ring

theorem mobiusLayerInner_symmetric (m n : ℕ) :
    mobiusLayerInner m n = mobiusLayerInner n m := by
  unfold mobiusLayerInner finiteKernelPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e eMem
  apply Finset.sum_congr rfl
  intro d dMem
  rw [fareyGcdKernel_symmetric]
  ring

theorem mobiusLayerInner_one_primePow
    {p k : ℕ} (pPrime : p.Prime) (kPositive : 0 < k) :
    mobiusLayerInner 1 (p ^ k)
      = -(p - 1 : ℚ) / (p ^ k : ℚ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero kPositive.ne'
  unfold mobiusLayerInner finiteKernelPairing
  simp only [Nat.divisors_one, Nat.succ_eq_add_one,
    Finset.sum_singleton, Order.lt_one_iff, Nat.div_self,
    isUnit_iff_eq_one, IsUnit.squarefree,
    ArithmeticFunction.moebius_apply_of_squarefree, Int.reduceNeg,
    ArithmeticFunction.cardFactors_one, pow_zero, Int.cast_one, one_mul,
    neg_sub]
  rw [Nat.sum_divisors_prime_pow pPrime]
  rw [show t + 1 = t.succ by omega]
  rw [moebiusPrimePower_weightedRange pPrime]
  have kernelAtT :
      fareyGcdKernel 1 (p ^ t) = (p ^ t : ℚ)⁻¹ := by
    simpa using
      (fareyGcdKernel_primePowers_of_le pPrime.pos (Nat.zero_le t))
  have kernelAtSucc :
      fareyGcdKernel 1 (p ^ t.succ) = (p ^ t.succ : ℚ)⁻¹ := by
    simpa using
      (fareyGcdKernel_primePowers_of_le pPrime.pos (Nat.zero_le t.succ))
  rw [kernelAtT, kernelAtSucc]
  have pCastNonzero : (p : ℚ) ≠ 0 := by
    exact_mod_cast pPrime.ne_zero
  field_simp [pCastNonzero, pow_succ]
  rw [pow_succ]
  ring

theorem mobiusLayerInner_primePow_one
    {p k : ℕ} (pPrime : p.Prime) (kPositive : 0 < k) :
    mobiusLayerInner (p ^ k) 1
      = -(p - 1 : ℚ) / (p ^ k : ℚ) := by
  rw [mobiusLayerInner_symmetric]
  exact mobiusLayerInner_one_primePow pPrime kPositive

theorem mobiusLayerInner_mul_of_crossCoprime
    {a b c d : ℕ} (crossCoprime : (a * c).Coprime (b * d)) :
    mobiusLayerInner (a * b) (c * d)
      = mobiusLayerInner a c * mobiusLayerInner b d := by
  have abCoprime : a.Coprime b :=
    (crossCoprime.coprime_dvd_left (dvd_mul_right a c)).coprime_dvd_right
      (dvd_mul_right b d)
  have cdCoprime : c.Coprime d :=
    (crossCoprime.coprime_dvd_left (dvd_mul_left c a)).coprime_dvd_right
      (dvd_mul_left d b)
  unfold mobiusLayerInner finiteKernelPairing
  rw [abCoprime.divisors_mul, cdCoprime.divisors_mul]
  simp only [Finset.sum_map]
  let pairTerm : (ℕ × ℕ) → (ℕ × ℕ) → ℚ :=
    fun dPair ePair =>
      (ArithmeticFunction.moebius
          (a * b / (dPair.1 * dPair.2)) : ℚ)
        * (ArithmeticFunction.moebius
            (c * d / (ePair.1 * ePair.2)) : ℚ)
        * fareyGcdKernel
            (dPair.1 * dPair.2) (ePair.1 * ePair.2)
  change
    (∑ dPair ∈ (a.divisors ×ˢ b.divisors).attach,
      ∑ ePair ∈ (c.divisors ×ˢ d.divisors).attach,
        pairTerm dPair ePair)
      =
    (∑ d₁ ∈ a.divisors, ∑ e₁ ∈ c.divisors,
      (ArithmeticFunction.moebius (a / d₁) : ℚ)
        * (ArithmeticFunction.moebius (c / e₁) : ℚ)
        * fareyGcdKernel d₁ e₁)
      *
    (∑ d₂ ∈ b.divisors, ∑ e₂ ∈ d.divisors,
      (ArithmeticFunction.moebius (b / d₂) : ℚ)
        * (ArithmeticFunction.moebius (d / e₂) : ℚ)
        * fareyGcdKernel d₂ e₂)
  have outerAttach :
      (∑ dPair ∈ (a.divisors ×ˢ b.divisors).attach,
        ∑ ePair ∈ (c.divisors ×ˢ d.divisors).attach,
          pairTerm dPair ePair)
        =
      ∑ dPair ∈ a.divisors ×ˢ b.divisors,
        ∑ ePair ∈ (c.divisors ×ˢ d.divisors).attach,
          pairTerm dPair ePair := by
    exact Finset.sum_attach
      (a.divisors ×ˢ b.divisors)
      (fun dPair : ℕ × ℕ =>
        (∑ ePair ∈ (c.divisors ×ˢ d.divisors).attach,
          pairTerm dPair ePair : ℚ))
  rw [outerAttach]
  have innerAttach (dPair : ℕ × ℕ) :
      (∑ ePair ∈ (c.divisors ×ˢ d.divisors).attach,
        pairTerm dPair ePair)
        =
      ∑ ePair ∈ c.divisors ×ˢ d.divisors,
        pairTerm dPair ePair := by
    exact Finset.sum_attach
      (c.divisors ×ˢ d.divisors)
      (fun ePair : ℕ × ℕ => pairTerm dPair ePair)
  simp_rw [innerAttach]
  change
    (∑ dPair ∈ a.divisors ×ˢ b.divisors,
      ∑ ePair ∈ c.divisors ×ˢ d.divisors,
        (ArithmeticFunction.moebius
            (a * b / (dPair.1 * dPair.2)) : ℚ)
          * (ArithmeticFunction.moebius
              (c * d / (ePair.1 * ePair.2)) : ℚ)
          * fareyGcdKernel
              (dPair.1 * dPair.2) (ePair.1 * ePair.2))
      =
    (∑ d₁ ∈ a.divisors, ∑ e₁ ∈ c.divisors,
      (ArithmeticFunction.moebius (a / d₁) : ℚ)
        * (ArithmeticFunction.moebius (c / e₁) : ℚ)
        * fareyGcdKernel d₁ e₁)
      *
    (∑ d₂ ∈ b.divisors, ∑ e₂ ∈ d.divisors,
      (ArithmeticFunction.moebius (b / d₂) : ℚ)
        * (ArithmeticFunction.moebius (d / e₂) : ℚ)
        * fareyGcdKernel d₂ e₂)
  let leftTerm : ℕ → ℕ → ℚ :=
    fun d₁ e₁ =>
      (ArithmeticFunction.moebius (a / d₁) : ℚ)
        * (ArithmeticFunction.moebius (c / e₁) : ℚ)
        * fareyGcdKernel d₁ e₁
  let rightTerm : ℕ → ℕ → ℚ :=
    fun d₂ e₂ =>
      (ArithmeticFunction.moebius (b / d₂) : ℚ)
        * (ArithmeticFunction.moebius (d / e₂) : ℚ)
        * fareyGcdKernel d₂ e₂
  have summandFactor
      (dPair ePair : ℕ × ℕ)
      (dMem : dPair ∈ a.divisors ×ˢ b.divisors)
      (eMem : ePair ∈ c.divisors ×ˢ d.divisors) :
      (ArithmeticFunction.moebius
          (a * b / (dPair.1 * dPair.2)) : ℚ)
        * (ArithmeticFunction.moebius
            (c * d / (ePair.1 * ePair.2)) : ℚ)
        * fareyGcdKernel
            (dPair.1 * dPair.2) (ePair.1 * ePair.2)
        =
      leftTerm dPair.1 ePair.1
        * rightTerm dPair.2 ePair.2 := by
    rcases Finset.mem_product.mp dMem with ⟨d₁Mem, d₂Mem⟩
    rcases Finset.mem_product.mp eMem with ⟨e₁Mem, e₂Mem⟩
    have d₁Dvd : dPair.1 ∣ a := Nat.dvd_of_mem_divisors d₁Mem
    have d₂Dvd : dPair.2 ∣ b := Nat.dvd_of_mem_divisors d₂Mem
    have e₁Dvd : ePair.1 ∣ c := Nat.dvd_of_mem_divisors e₁Mem
    have e₂Dvd : ePair.2 ∣ d := Nat.dvd_of_mem_divisors e₂Mem
    have dQuotCoprime : (a / dPair.1).Coprime (b / dPair.2) :=
      (abCoprime.coprime_dvd_left
        (Nat.div_dvd_of_dvd d₁Dvd)).coprime_dvd_right
          (Nat.div_dvd_of_dvd d₂Dvd)
    have eQuotCoprime : (c / ePair.1).Coprime (d / ePair.2) :=
      (cdCoprime.coprime_dvd_left
        (Nat.div_dvd_of_dvd e₁Dvd)).coprime_dvd_right
          (Nat.div_dvd_of_dvd e₂Dvd)
    have d₁CrossD₂ : dPair.1.Coprime dPair.2 :=
      (crossCoprime.coprime_dvd_left
        (d₁Dvd.trans (dvd_mul_right a c))).coprime_dvd_right
          (d₂Dvd.trans (dvd_mul_right b d))
    have e₁CrossE₂ : ePair.1.Coprime ePair.2 :=
      (crossCoprime.coprime_dvd_left
        (e₁Dvd.trans (dvd_mul_left c a))).coprime_dvd_right
          (e₂Dvd.trans (dvd_mul_left d b))
    have d₂CrossE₁ : dPair.2.Coprime ePair.1 :=
      ((crossCoprime.coprime_dvd_left
        (e₁Dvd.trans (dvd_mul_left c a))).coprime_dvd_right
          (d₂Dvd.trans (dvd_mul_right b d))).symm
    have d₁CrossE₂ : dPair.1.Coprime ePair.2 :=
      (crossCoprime.coprime_dvd_left
        (d₁Dvd.trans (dvd_mul_right a c))).coprime_dvd_right
          (e₂Dvd.trans (dvd_mul_left d b))
    have moebiusD :
        (ArithmeticFunction.moebius
            (a * b / (dPair.1 * dPair.2)) : ℚ)
          =
        (ArithmeticFunction.moebius (a / dPair.1) : ℚ)
          * (ArithmeticFunction.moebius (b / dPair.2) : ℚ) := by
      rw [← Nat.div_mul_div_comm d₁Dvd d₂Dvd]
      exact_mod_cast
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
          dQuotCoprime
    have moebiusE :
        (ArithmeticFunction.moebius
            (c * d / (ePair.1 * ePair.2)) : ℚ)
          =
        (ArithmeticFunction.moebius (c / ePair.1) : ℚ)
          * (ArithmeticFunction.moebius (d / ePair.2) : ℚ) := by
      rw [← Nat.div_mul_div_comm e₁Dvd e₂Dvd]
      exact_mod_cast
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
          eQuotCoprime
    rw [moebiusD, moebiusE,
      fareyGcdKernel_mul_of_crossCoprime d₁CrossD₂ e₁CrossE₂
        d₂CrossE₁ d₁CrossE₂]
    unfold leftTerm rightTerm
    ring
  calc
    (∑ dPair ∈ a.divisors ×ˢ b.divisors,
      ∑ ePair ∈ c.divisors ×ˢ d.divisors,
        (ArithmeticFunction.moebius
            (a * b / (dPair.1 * dPair.2)) : ℚ)
          * (ArithmeticFunction.moebius
              (c * d / (ePair.1 * ePair.2)) : ℚ)
          * fareyGcdKernel
              (dPair.1 * dPair.2) (ePair.1 * ePair.2))
        =
      ∑ dPair ∈ a.divisors ×ˢ b.divisors,
        ∑ ePair ∈ c.divisors ×ˢ d.divisors,
          leftTerm dPair.1 ePair.1
            * rightTerm dPair.2 ePair.2 := by
              apply Finset.sum_congr rfl
              intro dPair dMem
              apply Finset.sum_congr rfl
              intro ePair eMem
              exact summandFactor dPair ePair dMem eMem
    _ =
      ∑ d₁ ∈ a.divisors, ∑ d₂ ∈ b.divisors,
        ∑ e₁ ∈ c.divisors, ∑ e₂ ∈ d.divisors,
          leftTerm d₁ e₁ * rightTerm d₂ e₂ := by
            simp_rw [Finset.sum_product]
    _ =
      ∑ d₁ ∈ a.divisors, ∑ e₁ ∈ c.divisors,
        ∑ d₂ ∈ b.divisors, ∑ e₂ ∈ d.divisors,
          leftTerm d₁ e₁ * rightTerm d₂ e₂ := by
            apply Finset.sum_congr rfl
            intro d₁ d₁Mem
            rw [Finset.sum_comm]
    _ =
      (∑ d₁ ∈ a.divisors, ∑ e₁ ∈ c.divisors,
        leftTerm d₁ e₁)
        *
      (∑ d₂ ∈ b.divisors, ∑ e₂ ∈ d.divisors,
        rightTerm d₂ e₂) := by
            symm
            simp_rw [Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro d₁ d₁Mem
            rw [Finset.sum_comm]
    _ =
      (∑ d₁ ∈ a.divisors, ∑ e₁ ∈ c.divisors,
        (ArithmeticFunction.moebius (a / d₁) : ℚ)
          * (ArithmeticFunction.moebius (c / e₁) : ℚ)
          * fareyGcdKernel d₁ e₁)
        *
      (∑ d₂ ∈ b.divisors, ∑ e₂ ∈ d.divisors,
        (ArithmeticFunction.moebius (b / d₂) : ℚ)
          * (ArithmeticFunction.moebius (d / e₂) : ℚ)
          * fareyGcdKernel d₂ e₂) := by
            rfl

/-- The first row of the Möbius-layer Gram matrix as an arithmetic function. -/
noncomputable def mobiusLayerFirstRowQ : ArithmeticFunction ℚ where
  toFun n := mobiusLayerInner n 1
  map_zero' := by
    simp [mobiusLayerInner, finiteKernelPairing]

@[simp]
theorem mobiusLayerFirstRowQ_apply (n : ℕ) :
    mobiusLayerFirstRowQ n = mobiusLayerInner n 1 := rfl

/-- The first Möbius-layer Gram row is exactly the Farey convolution arithmetic function. -/
theorem mobiusLayerInner_one_eq_fareyConvolutionCoeff (n : ℕ) :
    mobiusLayerInner n 1 =
      MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff n := by
  by_cases hn : n = 0
  · simp [hn, mobiusLayerInner, finiteKernelPairing,
      MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff]
  · unfold mobiusLayerInner finiteKernelPairing
    simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_one,
      ArithmeticFunction.moebius_apply_one, Int.cast_one, mul_one]
    unfold MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff
    rw [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal'
      (f := fun x y => (ArithmeticFunction.moebius : ArithmeticFunction ℚ) x *
        MathlibPlus.NumberTheory.Claim9757.reciprocalIndexQ y)]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : d ≠ 0 := by
      exact (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
        (Nat.pos_of_ne_zero hn)).ne'
    rw [fareyGcdKernel, Nat.gcd_one_right]
    simp [MathlibPlus.NumberTheory.Claim9757.reciprocalIndexQ, hd0]

/-- Arithmetic-function form of the exact Farey/Gram identification. -/
theorem mobiusLayerFirstRowQ_eq_fareyConvolutionCoeff :
    mobiusLayerFirstRowQ =
      MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff := by
  ext n
  exact mobiusLayerInner_one_eq_fareyConvolutionCoeff n

theorem mobiusLayerFirstRowQ_one :
    mobiusLayerFirstRowQ 1 = 1 := by
  rw [mobiusLayerFirstRowQ_eq_fareyConvolutionCoeff]
  exact MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff_isMultiplicative.map_one

theorem isMultiplicative_mobiusLayerFirstRowQ :
    ArithmeticFunction.IsMultiplicative mobiusLayerFirstRowQ := by
  rw [mobiusLayerFirstRowQ_eq_fareyConvolutionCoeff]
  exact MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff_isMultiplicative

theorem mobiusLayerFirstRowQ_primePow
    {p k : ℕ} (pPrime : p.Prime) (kPositive : 0 < k) :
    mobiusLayerFirstRowQ (p ^ k)
      = -(p - 1 : ℚ) / (p ^ k : ℚ) := by
  rw [mobiusLayerFirstRowQ_eq_fareyConvolutionCoeff]
  exact MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff_prime_pow pPrime kPositive

theorem mobiusLayerFirstRowQ_factorization
    {n : ℕ} (nPositive : 0 < n) :
    mobiusLayerInner n 1
      =
    n.factorization.prod
      (fun p k => -(p - 1 : ℚ) / (p ^ k : ℚ)) := by
  rw [← mobiusLayerFirstRowQ_apply,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      mobiusLayerFirstRowQ isMultiplicative_mobiusLayerFirstRowQ
      nPositive.ne']
  apply Finsupp.prod_congr
  intro p pMem
  have pPrime : p.Prime := Nat.prime_of_mem_primeFactors pMem
  have exponentPositive :
      0 < n.factorization p := by
    exact Finsupp.mem_support_iff.mp pMem |> Nat.pos_of_ne_zero
  exact mobiusLayerFirstRowQ_primePow pPrime exponentPositive

/-- Exact first Gram-row formula for admitted claim 42717, on its stated positive domain. -/
theorem mobiusLayerFirstRowQ_radical_formula_claim42717
    (m : ℕ) (_mPositive : 1 ≤ m) :
    mobiusLayerInner m 1 =
      (ArithmeticFunction.moebius (radical m) : ℚ)
        * (Nat.totient (radical m) : ℚ) / m := by
  rw [mobiusLayerInner_one_eq_fareyConvolutionCoeff]
  exact MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff_radical_formula m

end MathlibPlus.Analysis.Claim42717
