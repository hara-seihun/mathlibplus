import Mathlib

set_option linter.style.header false

namespace MathlibPlus.Analysis.O0332

noncomputable section

/-- The Cayley coordinate used for the pole relocation. -/
def cayleyCoordinate (rho : ℂ) : ℂ :=
  1 - rho⁻¹

/-- One quadratic factor in O-0332's rational all-pass product. -/
def allPassQuadraticFactor
    (c gamma : ℝ)
    (u : ℂ) : ℂ :=
  (((u - c) ^ 2 + gamma ^ 2)
    / ((u + c) ^ 2 + gamma ^ 2))

private theorem boundaryNumerator_expansion
    (c gamma tau : ℝ) :
    (((tau : ℂ) * Complex.I - c) ^ 2 + gamma ^ 2)
      =
    ((c ^ 2 - tau ^ 2 + gamma ^ 2 : ℝ) : ℂ)
      - (2 * c * tau : ℝ) * Complex.I := by
  apply Complex.ext
  all_goals
    (simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring)

private theorem boundaryDenominator_expansion
    (c gamma tau : ℝ) :
    (((tau : ℂ) * Complex.I + c) ^ 2 + gamma ^ 2)
      =
    ((c ^ 2 - tau ^ 2 + gamma ^ 2 : ℝ) : ℂ)
      + (2 * c * tau : ℝ) * Complex.I := by
  apply Complex.ext
  all_goals
    (simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring)

/-- On the imaginary axis, the numerator and denominator of one all-pass
quadratic factor have the same squared norm. -/
theorem allPassQuadraticFactor_boundary_normSq_numerator_eq_denominator
    (c gamma tau : ℝ) :
    Complex.normSq
        ((((tau : ℂ) * Complex.I - c) ^ 2 + gamma ^ 2))
      =
    Complex.normSq
        ((((tau : ℂ) * Complex.I + c) ^ 2 + gamma ^ 2)) := by
  rw [boundaryNumerator_expansion, boundaryDenominator_expansion]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, sub_zero, zero_add, mul_one]
  ring

/-- The stable denominator of one all-pass factor cannot vanish on the
imaginary axis when its real shift is positive. -/
theorem allPassQuadraticFactor_boundary_denominator_ne_zero
    {c gamma tau : ℝ}
    (positiveC : 0 < c) :
    (((tau : ℂ) * Complex.I + c) ^ 2 + gamma ^ 2) ≠ 0 := by
  intro denominatorZero
  rw [boundaryDenominator_expansion] at denominatorZero
  have imaginaryPartZero :=
    congrArg Complex.im denominatorZero
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_mul, mul_one,
    zero_add, Complex.zero_im] at imaginaryPartZero
  have tauZero : tau = 0 := by
    nlinarith
  have realPartZero :=
    congrArg Complex.re denominatorZero
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, Complex.zero_re] at realPartZero
  nlinarith [sq_nonneg gamma]

/-- Every positive-shift quadratic factor has exact unit squared norm on
the Fourier boundary. -/
theorem allPassQuadraticFactor_boundary_normSq_eq_one
    {c gamma tau : ℝ}
    (positiveC : 0 < c) :
    Complex.normSq
        (allPassQuadraticFactor c gamma
          ((tau : ℂ) * Complex.I))
      =
    1 := by
  have denominatorNeZero :=
    allPassQuadraticFactor_boundary_denominator_ne_zero
      (gamma := gamma) (tau := tau) positiveC
  have denominatorNormSqNeZero :
      Complex.normSq
          ((((tau : ℂ) * Complex.I + c) ^ 2 + gamma ^ 2))
        ≠ 0 :=
    (Complex.normSq_pos.mpr denominatorNeZero).ne'
  rw [allPassQuadraticFactor, Complex.normSq_div,
    div_eq_one_iff_eq denominatorNormSqNeZero]
  exact
    allPassQuadraticFactor_boundary_normSq_numerator_eq_denominator
      c gamma tau

/-- One positive-shift quadratic factor is normalized to one at the
Laplace origin. -/
theorem allPassQuadraticFactor_zero_eq_one
    {c gamma : ℝ}
    (positiveC : 0 < c) :
    allPassQuadraticFactor c gamma 0 = 1 := by
  have denominatorNeZero :
      (((0 : ℂ) + c) ^ 2 + gamma ^ 2) ≠ 0 := by
    simpa using
      (allPassQuadraticFactor_boundary_denominator_ne_zero
        (gamma := gamma) (tau := 0) positiveC)
  have numeratorEqDenominator :
      (((0 : ℂ) - c) ^ 2 + gamma ^ 2)
        =
      (((0 : ℂ) + c) ^ 2 + gamma ^ 2) := by
    ring
  rw [allPassQuadraticFactor, numeratorEqDenominator,
    div_self denominatorNeZero]

/-- O-0332's full functional-equation-paired rational all-pass product. -/
def allPassProduct
    (a gamma : ℝ)
    (u : ℂ) : ℂ :=
  allPassQuadraticFactor a gamma u
    * allPassQuadraticFactor (1 - a) gamma u

/-- The full product preserves exact squared modulus on the imaginary
boundary. -/
theorem allPassProduct_boundary_normSq_eq_one
    {a gamma tau : ℝ}
    (positiveA : 0 < a)
    (aLtHalf : a < 1 / 2) :
    Complex.normSq
        (allPassProduct a gamma ((tau : ℂ) * Complex.I))
      =
    1 := by
  have partnerShiftPositive : 0 < 1 - a := by
    linarith
  rw [allPassProduct, Complex.normSq_mul,
    allPassQuadraticFactor_boundary_normSq_eq_one positiveA,
    allPassQuadraticFactor_boundary_normSq_eq_one partnerShiftPositive,
    one_mul]

/-- The all-pass product preserves the source integral because it is
normalized to one at the Laplace origin. -/
theorem allPassProduct_zero_eq_one
    {a gamma : ℝ}
    (positiveA : 0 < a)
    (aLtHalf : a < 1 / 2) :
    allPassProduct a gamma 0 = 1 := by
  have partnerShiftPositive : 0 < 1 - a := by
    linarith
  rw [allPassProduct, allPassQuadraticFactor_zero_eq_one positiveA,
    allPassQuadraticFactor_zero_eq_one partnerShiftPositive, one_mul]

/-- Factorization of one stable quadratic denominator into its two complex
linear roots. -/
theorem allPassQuadraticDenominator_factorization
    (c gamma : ℝ)
    (u : ℂ) :
    (u + c) ^ 2 + gamma ^ 2
      =
    (u + c - (gamma : ℂ) * Complex.I)
      * (u + c + (gamma : ℂ) * Complex.I) := by
  calc
    (u + c) ^ 2 + gamma ^ 2
        =
      (u + c) ^ 2 - ((gamma : ℂ) * Complex.I) ^ 2 := by
        rw [mul_pow, Complex.I_sq]
        ring
    _ =
      (u + c - (gamma : ℂ) * Complex.I)
        * (u + c + (gamma : ℂ) * Complex.I) := by
          ring

/-- The stable quadratic denominator vanishes exactly at its conjugate
left-half-plane pair. -/
theorem allPassQuadraticDenominator_eq_zero_iff
    (c gamma : ℝ)
    (u : ℂ) :
    (u + c) ^ 2 + gamma ^ 2 = 0
      ↔
    u = -(c : ℂ) + (gamma : ℂ) * Complex.I
      ∨
    u = -(c : ℂ) - (gamma : ℂ) * Complex.I := by
  rw [allPassQuadraticDenominator_factorization, mul_eq_zero]
  constructor
  · intro root
    rcases root with root | root
    · left
      linear_combination root
    · right
      linear_combination root
  · intro root
    rcases root with root | root
    · left
      linear_combination root
    · right
      linear_combination root

/-- Every root of a positive-shift quadratic denominator lies on the
vertical line with real part `-c`. -/
theorem allPassQuadraticDenominator_root_re
    {c gamma : ℝ}
    {u : ℂ}
    (denominatorRoot : (u + c) ^ 2 + gamma ^ 2 = 0) :
    u.re = -c := by
  rcases
    (allPassQuadraticDenominator_eq_zero_iff
      c gamma u).mp denominatorRoot with root | root
  · subst u
    simp
  · subst u
    simp

/-- The algebraic derivative of `(u+c)^2+gamma^2`. -/
def allPassQuadraticDenominatorDerivative
    (c : ℝ)
    (u : ℂ) : ℂ :=
  2 * (u + c)

/-- For nonzero frequency, both conjugate denominator roots are simple. -/
theorem allPassQuadraticDenominatorDerivative_ne_zero_at_root
    {c gamma : ℝ}
    {u : ℂ}
    (gammaNeZero : gamma ≠ 0)
    (denominatorRoot : (u + c) ^ 2 + gamma ^ 2 = 0) :
    allPassQuadraticDenominatorDerivative c u ≠ 0 := by
  rcases
    (allPassQuadraticDenominator_eq_zero_iff
      c gamma u).mp denominatorRoot with root | root
  · subst u
    have derivativeValue :
        allPassQuadraticDenominatorDerivative c
            (-(c : ℂ) + (gamma : ℂ) * Complex.I)
          =
        ((2 * gamma : ℝ) : ℂ) * Complex.I := by
      unfold allPassQuadraticDenominatorDerivative
      push_cast
      ring
    rw [derivativeValue]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (by norm_num) gammaNeZero))
      Complex.I_ne_zero
  · subst u
    have derivativeValue :
        allPassQuadraticDenominatorDerivative c
            (-(c : ℂ) - (gamma : ℂ) * Complex.I)
          =
        -(((2 * gamma : ℝ) : ℂ) * Complex.I) := by
      unfold allPassQuadraticDenominatorDerivative
      push_cast
      ring
    rw [derivativeValue]
    exact neg_ne_zero.mpr <|
      mul_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (mul_ne_zero (by norm_num) gammaNeZero))
        Complex.I_ne_zero

/-- Factorization of one reflected quadratic numerator. -/
theorem allPassQuadraticNumerator_factorization
    (c gamma : ℝ)
    (u : ℂ) :
    (u - c) ^ 2 + gamma ^ 2
      =
    (u - c - (gamma : ℂ) * Complex.I)
      * (u - c + (gamma : ℂ) * Complex.I) := by
  calc
    (u - c) ^ 2 + gamma ^ 2
        =
      (u - c) ^ 2 - ((gamma : ℂ) * Complex.I) ^ 2 := by
        rw [mul_pow, Complex.I_sq]
        ring
    _ =
      (u - c - (gamma : ℂ) * Complex.I)
        * (u - c + (gamma : ℂ) * Complex.I) := by
          ring

/-- Every numerator root has positive real part `c`; consequently a
positive-shift numerator cannot vanish in the open left half-plane. -/
theorem allPassQuadraticNumerator_ne_zero_of_re_neg
    {c gamma : ℝ}
    {u : ℂ}
    (positiveC : 0 < c)
    (negativeRealPart : u.re < 0) :
    (u - c) ^ 2 + gamma ^ 2 ≠ 0 := by
  intro numeratorZero
  rw [allPassQuadraticNumerator_factorization, mul_eq_zero] at numeratorZero
  rcases numeratorZero with numeratorZero | numeratorZero
  · have realPartIdentity := congrArg Complex.re numeratorZero
    simp only [Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, Complex.zero_re] at realPartIdentity
    linarith
  · have realPartIdentity := congrArg Complex.re numeratorZero
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, Complex.zero_re] at realPartIdentity
    linarith

/-- Numerator of the full paired rational all-pass product. -/
def allPassProductNumerator
    (a gamma : ℝ)
    (u : ℂ) : ℂ :=
  ((u - a) ^ 2 + gamma ^ 2)
    * ((u - (1 - a)) ^ 2 + gamma ^ 2)

/-- Denominator of the full paired rational all-pass product. -/
def allPassProductDenominator
    (a gamma : ℝ)
    (u : ℂ) : ℂ :=
  ((u + a) ^ 2 + gamma ^ 2)
    * ((u + (1 - a)) ^ 2 + gamma ^ 2)

theorem allPassProduct_eq_numerator_div_denominator
    (a gamma : ℝ)
    (u : ℂ) :
    allPassProduct a gamma u
      =
    allPassProductNumerator a gamma u
      / allPassProductDenominator a gamma u := by
  simp only [allPassProduct, allPassQuadraticFactor,
    allPassProductNumerator, allPassProductDenominator, div_mul_div_comm]
  push_cast
  rfl

/-- The full denominator has exactly the conjugate and
functional-equation-paired four-point root locus. -/
theorem allPassProductDenominator_eq_zero_iff
    (a gamma : ℝ)
    (u : ℂ) :
    allPassProductDenominator a gamma u = 0
      ↔
    u = -(a : ℂ) + (gamma : ℂ) * Complex.I
      ∨
    u = -(a : ℂ) - (gamma : ℂ) * Complex.I
      ∨
    u = -((1 - a : ℝ) : ℂ) + (gamma : ℂ) * Complex.I
      ∨
    u = -((1 - a : ℝ) : ℂ) - (gamma : ℂ) * Complex.I := by
  rw [allPassProductDenominator, mul_eq_zero]
  constructor
  · intro denominatorRoot
    rcases denominatorRoot with firstRoot | secondRoot
    · rcases
        (allPassQuadraticDenominator_eq_zero_iff a gamma u).mp firstRoot
          with root | root
      · exact Or.inl root
      · exact Or.inr (Or.inl root)
    · have normalizedSecondRoot :
          (u + ((1 - a : ℝ) : ℂ)) ^ 2 + gamma ^ 2 = 0 := by
        simpa only [Complex.ofReal_sub, Complex.ofReal_one] using secondRoot
      rcases
        (allPassQuadraticDenominator_eq_zero_iff
          (1 - a) gamma u).mp normalizedSecondRoot
          with root | root
      · exact Or.inr (Or.inr (Or.inl root))
      · exact Or.inr (Or.inr (Or.inr root))
  · intro root
    rcases root with root | root | root | root
    · left
      exact
        (allPassQuadraticDenominator_eq_zero_iff a gamma u).mpr
          (Or.inl root)
    · left
      exact
        (allPassQuadraticDenominator_eq_zero_iff a gamma u).mpr
          (Or.inr root)
    · right
      have normalizedSecondRoot :=
        (allPassQuadraticDenominator_eq_zero_iff
          (1 - a) gamma u).mpr (Or.inl root)
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
        normalizedSecondRoot
    · right
      have normalizedSecondRoot :=
        (allPassQuadraticDenominator_eq_zero_iff
          (1 - a) gamma u).mpr (Or.inr root)
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
        normalizedSecondRoot

/-- The two paired denominator quadratics have no common root when
`0<a<1/2`. -/
theorem allPassPairedQuadraticDenominators_no_common_root
    {a gamma : ℝ}
    {u : ℂ}
    (aLtHalf : a < 1 / 2) :
    ¬
      ((u + a) ^ 2 + gamma ^ 2 = 0
        ∧
      (u + (1 - a)) ^ 2 + gamma ^ 2 = 0) := by
  intro commonRoot
  have firstRealPart :
      u.re = -a :=
    allPassQuadraticDenominator_root_re commonRoot.1
  have normalizedSecondRoot :
      (u + ((1 - a : ℝ) : ℂ)) ^ 2 + gamma ^ 2 = 0 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using commonRoot.2
  have secondRealPart :
      u.re = -(1 - a) :=
    allPassQuadraticDenominator_root_re normalizedSecondRoot
  linarith

/-- The formal derivative of the paired denominator product. -/
def allPassProductDenominatorDerivative
    (a gamma : ℝ)
    (u : ℂ) : ℂ :=
  allPassQuadraticDenominatorDerivative a u
      * ((u + (1 - a)) ^ 2 + gamma ^ 2)
    +
  ((u + a) ^ 2 + gamma ^ 2)
      * allPassQuadraticDenominatorDerivative (1 - a) u

/-- For `0<a<1/2` and positive frequency, every root of the full paired
denominator is algebraically simple. -/
theorem allPassProductDenominatorDerivative_ne_zero_at_root
    {a gamma : ℝ}
    {u : ℂ}
    (aLtHalf : a < 1 / 2)
    (gammaPositive : 0 < gamma)
    (denominatorRoot : allPassProductDenominator a gamma u = 0) :
    allPassProductDenominatorDerivative a gamma u ≠ 0 := by
  have gammaNeZero : gamma ≠ 0 := gammaPositive.ne'
  rw [allPassProductDenominator, mul_eq_zero] at denominatorRoot
  rcases denominatorRoot with firstRoot | secondRoot
  · have secondNeZero :
        (u + (1 - a)) ^ 2 + gamma ^ 2 ≠ 0 := by
      intro secondRoot
      exact
        allPassPairedQuadraticDenominators_no_common_root aLtHalf
          ⟨firstRoot, secondRoot⟩
    have firstDerivativeNeZero :
        allPassQuadraticDenominatorDerivative a u ≠ 0 :=
      allPassQuadraticDenominatorDerivative_ne_zero_at_root
        gammaNeZero firstRoot
    unfold allPassProductDenominatorDerivative
    rw [firstRoot, zero_mul, add_zero]
    exact mul_ne_zero firstDerivativeNeZero secondNeZero
  · have firstNeZero :
        (u + a) ^ 2 + gamma ^ 2 ≠ 0 := by
      intro firstRoot
      exact
        allPassPairedQuadraticDenominators_no_common_root aLtHalf
          ⟨firstRoot, secondRoot⟩
    have normalizedSecondRoot :
        (u + ((1 - a : ℝ) : ℂ)) ^ 2 + gamma ^ 2 = 0 := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using secondRoot
    have secondDerivativeNeZero :
        allPassQuadraticDenominatorDerivative (1 - a) u ≠ 0 :=
      allPassQuadraticDenominatorDerivative_ne_zero_at_root
        gammaNeZero normalizedSecondRoot
    unfold allPassProductDenominatorDerivative
    rw [secondRoot, mul_zero, zero_add]
    exact mul_ne_zero firstNeZero secondDerivativeNeZero

/-- None of the four denominator roots is cancelled by the paired
numerator when `0<a<1/2`. -/
theorem allPassProductNumerator_ne_zero_at_denominator_root
    {a gamma : ℝ}
    {u : ℂ}
    (positiveA : 0 < a)
    (aLtHalf : a < 1 / 2)
    (denominatorRoot : allPassProductDenominator a gamma u = 0) :
    allPassProductNumerator a gamma u ≠ 0 := by
  have partnerShiftPositive : 0 < 1 - a := by
    linarith
  have negativeRealPart : u.re < 0 := by
    rw [allPassProductDenominator, mul_eq_zero] at denominatorRoot
    rcases denominatorRoot with firstRoot | secondRoot
    · rcases
        (allPassQuadraticDenominator_eq_zero_iff
          a gamma u).mp firstRoot with root | root
      · subst u
        simpa using (neg_lt_zero.mpr positiveA)
      · subst u
        simpa using (neg_lt_zero.mpr positiveA)
    · have normalizedSecondRoot :
          (u + ((1 - a : ℝ) : ℂ)) ^ 2 + gamma ^ 2 = 0 := by
        simpa only [Complex.ofReal_sub, Complex.ofReal_one] using secondRoot
      rcases
        (allPassQuadraticDenominator_eq_zero_iff
          (1 - a) gamma u).mp normalizedSecondRoot with root | root
      · subst u
        simpa using (neg_lt_zero.mpr partnerShiftPositive)
      · subst u
        simpa using (neg_lt_zero.mpr partnerShiftPositive)
  unfold allPassProductNumerator
  apply mul_ne_zero
  · exact
      allPassQuadraticNumerator_ne_zero_of_re_neg
        (gamma := gamma) positiveA negativeRealPart
  · have partnerNumeratorNeZero :
        (u - ((1 - a : ℝ) : ℂ)) ^ 2 + gamma ^ 2 ≠ 0 :=
      allPassQuadraticNumerator_ne_zero_of_re_neg
        (gamma := gamma) partnerShiftPositive negativeRealPart
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      partnerNumeratorNeZero

/-- The Cayley image of the right-of-line pole
`-a + i gamma = ((1-a)+i gamma)-1`. -/
def innerPoleCayley (a gamma : ℝ) : ℂ :=
  cayleyCoordinate
    (((1 - a : ℝ) : ℂ) + (gamma : ℂ) * Complex.I)

/-- The Cayley image of the functional-equation partner pole
`-(1-a) + i gamma = (a+i gamma)-1`. -/
def partnerPoleCayley (a gamma : ℝ) : ℂ :=
  cayleyCoordinate
    ((a : ℂ) + (gamma : ℂ) * Complex.I)

theorem innerPoleCayley_normSq
    {a gamma : ℝ}
    (aLtHalf : a < 1 / 2) :
    Complex.normSq (innerPoleCayley a gamma)
      =
    (a ^ 2 + gamma ^ 2)
      / ((1 - a) ^ 2 + gamma ^ 2) := by
  have rhoNeZero :
      (((1 - a : ℝ) : ℂ) + (gamma : ℂ) * Complex.I) ≠ 0 := by
    intro rhoZero
    have realPartZero := congrArg Complex.re rhoZero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, Complex.zero_re] at realPartZero
    linarith
  have coordinateAsQuotient :
      innerPoleCayley a gamma
        =
      ((((1 - a : ℝ) : ℂ) + (gamma : ℂ) * Complex.I) - 1)
        / (((1 - a : ℝ) : ℂ) + (gamma : ℂ) * Complex.I) := by
    rw [innerPoleCayley, cayleyCoordinate]
    apply (eq_div_iff rhoNeZero).2
    rw [sub_mul, one_mul, inv_mul_cancel₀ rhoNeZero]
  rw [coordinateAsQuotient, Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, mul_zero, add_zero, sub_zero, zero_add,
    mul_one]
  ring

theorem partnerPoleCayley_normSq
    {a gamma : ℝ}
    (positiveA : 0 < a) :
    Complex.normSq (partnerPoleCayley a gamma)
      =
    ((1 - a) ^ 2 + gamma ^ 2)
      / (a ^ 2 + gamma ^ 2) := by
  have rhoNeZero :
      ((a : ℂ) + (gamma : ℂ) * Complex.I) ≠ 0 := by
    intro rhoZero
    have realPartZero := congrArg Complex.re rhoZero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, Complex.zero_re] at realPartZero
    linarith
  have coordinateAsQuotient :
      partnerPoleCayley a gamma
        =
      (((a : ℂ) + (gamma : ℂ) * Complex.I) - 1)
        / ((a : ℂ) + (gamma : ℂ) * Complex.I) := by
    rw [partnerPoleCayley, cayleyCoordinate]
    apply (eq_div_iff rhoNeZero).2
    rw [sub_mul, one_mul, inv_mul_cancel₀ rhoNeZero]
  rw [coordinateAsQuotient, Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, mul_zero, add_zero, sub_zero, zero_add,
    mul_one]
  ring

/-- For `0<a<1/2`, the pole with real part `-a` maps strictly inside the
Cayley unit disk. -/
theorem innerPoleCayley_normSq_lt_one
    {a gamma : ℝ}
    (positiveA : 0 < a)
    (aLtHalf : a < 1 / 2) :
    Complex.normSq (innerPoleCayley a gamma) < 1 := by
  rw [innerPoleCayley_normSq aLtHalf]
  have denominatorPositive :
      0 < (1 - a) ^ 2 + gamma ^ 2 := by
    nlinarith [sq_nonneg gamma]
  rw [div_lt_one denominatorPositive]
  nlinarith

/-- The functional-equation partner pole maps strictly outside the Cayley
unit disk. -/
theorem one_lt_partnerPoleCayley_normSq
    {a gamma : ℝ}
    (positiveA : 0 < a)
    (aLtHalf : a < 1 / 2) :
    1 < Complex.normSq (partnerPoleCayley a gamma) := by
  rw [partnerPoleCayley_normSq positiveA]
  have denominatorPositive :
      0 < a ^ 2 + gamma ^ 2 := by
    nlinarith [sq_nonneg gamma]
  rw [one_lt_div denominatorPositive]
  nlinarith

/-- The Poisson-square exponential rate carried by O-0332's inner pole. -/
def allPassFockRate (a gamma : ℝ) : ℝ :=
  (Complex.normSq (innerPoleCayley a gamma))⁻¹ - 1

theorem allPassFockRate_eq
    {a gamma : ℝ}
    (positiveA : 0 < a)
    (aLtHalf : a < 1 / 2) :
    allPassFockRate a gamma
      =
    (1 - 2 * a) / (a ^ 2 + gamma ^ 2) := by
  have numeratorPositive :
      0 < a ^ 2 + gamma ^ 2 := by
    nlinarith [sq_nonneg gamma]
  have denominatorPositive :
      0 < (1 - a) ^ 2 + gamma ^ 2 := by
    nlinarith [sq_nonneg gamma]
  rw [allPassFockRate, innerPoleCayley_normSq aLtHalf]
  field_simp [numeratorPositive.ne', denominatorPositive.ne']
  ring

theorem allPassFockRate_pos
    {a gamma : ℝ}
    (positiveA : 0 < a)
    (aLtHalf : a < 1 / 2) :
    0 < allPassFockRate a gamma := by
  rw [allPassFockRate_eq positiveA aLtHalf]
  have denominatorPositive :
      0 < a ^ 2 + gamma ^ 2 := by
    nlinarith [sq_nonneg gamma]
  exact div_pos (by linarith) denominatorPositive

end

end MathlibPlus.Analysis.O0332
