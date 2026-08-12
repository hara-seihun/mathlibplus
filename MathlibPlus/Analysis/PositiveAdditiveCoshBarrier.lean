import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim19057

/-- The source's phrase "closed under positive addition" is made explicit as
closure under pointwise addition and multiplication by a strictly positive real
scalar. -/
theorem positiveAdditive_contains_coshBarrier_claim19057
    (F : Set (ℂ → ℂ)) (c a : ℝ)
    (hadd : ∀ f g : ℂ → ℂ, f ∈ F → g ∈ F →
      (fun z => f z + g z) ∈ F)
    (hsmul : ∀ (r : ℝ) (f : ℂ → ℂ), 0 < r → f ∈ F →
      (fun z => (r : ℂ) * f z) ∈ F)
    (hconst : ∀ b : ℝ, 0 < b → (fun _ : ℂ => (b : ℂ)) ∈ F)
    (hexp : (fun z : ℂ => Complex.exp ((a : ℂ) * z)) ∈ F ∧
      (fun z : ℂ => Complex.exp (-((a : ℂ) * z))) ∈ F)
    (hc : 0 < c) :
    (fun z : ℂ => (c : ℂ) + Complex.cosh ((a : ℂ) * z)) ∈ F := by
  have hplus := hsmul (1 / 2 : ℝ) _ (by norm_num) hexp.1
  have hminus := hsmul (1 / 2 : ℝ) _ (by norm_num) hexp.2
  have hpair := hadd _ _ hplus hminus
  have hconstant := hconst c hc
  have htotal := hadd _ _ hconstant hpair
  simpa [Complex.cosh, div_eq_mul_inv, mul_add, add_mul, add_assoc,
    add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using htotal

/-- One of the explicit off-axis zeros in claim 19057.  The full infinitely
many-zero assertion is retained below as an open registry node. -/
theorem cplusCosh_firstOffAxisZero_claim19057 (c a : ℝ)
    (hc : 1 < c) (ha : 0 < a) :
    (c : ℂ) + Complex.cosh ((a : ℂ) *
      (((Real.arcosh c : ℂ) + (Real.pi : ℂ) * Complex.I) / (a : ℂ))) = 0 := by
  have harcosh : Complex.cosh (Real.arcosh c : ℂ) = (c : ℂ) := by
    apply Complex.ext
    · simpa using Real.cosh_arcosh hc.le
    · simp
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have harg : (a : ℂ) *
      (((Real.arcosh c : ℂ) + (Real.pi : ℂ) * Complex.I) / (a : ℂ)) =
      (Real.arcosh c : ℂ) + (Real.pi : ℂ) * Complex.I := by
    field_simp [ha0]
  rw [harg, Complex.cosh_add_pi_mul_I, harcosh]
  norm_num

end MathlibPlus.Analysis.Claim19057

namespace MathlibPlus.Open.Analysis

/-- Claim 19057.  The positive-additive closure and the imaginary-axis
positivity are explicit; the source's phrase "reflected exponential pair" is
represented by the two displayed exponentials.  The real powers and the
infinitely many off-axis zeros are not weakened. -/
def positiveAdditiveCoshBarrier_claim19057 : Prop :=
  ∀ (F : Set (ℂ → ℂ)) (c a : ℝ),
    (∀ f g : ℂ → ℂ, f ∈ F → g ∈ F →
      (fun z => f z + g z) ∈ F) →
    (∀ (r : ℝ) (f : ℂ → ℂ), 0 < r → f ∈ F →
      (fun z => (r : ℂ) * f z) ∈ F) →
    (∀ b : ℝ, 0 < b → (fun _ : ℂ => (b : ℂ)) ∈ F) →
    ((fun z : ℂ => Complex.exp ((a : ℂ) * z)) ∈ F ∧
      (fun z : ℂ => Complex.exp (-((a : ℂ) * z))) ∈ F) →
    1 < c → 0 < a →
    (fun z : ℂ => (c : ℂ) + Complex.cosh ((a : ℂ) * z)) ∈ F ∧
    (∀ t : ℝ, 0 <
      ((c : ℂ) + Complex.cosh ((a : ℂ) * ((t : ℂ) * Complex.I))).re) ∧
    (∀ k : ℤ,
      (c : ℂ) + Complex.cosh ((a : ℂ) *
        (((Real.arcosh c : ℂ) +
          ((((2 * k + 1 : ℤ) : ℝ) * Real.pi : ℂ) * Complex.I)) /
            (a : ℂ))) = 0 ∧
      (c : ℂ) + Complex.cosh ((a : ℂ) *
        (((-(Real.arcosh c) : ℂ) +
          ((((2 * k + 1 : ℤ) : ℝ) * Real.pi : ℂ) * Complex.I)) /
            (a : ℂ))) = 0) ∧
    Set.Infinite {z : ℂ |
      (c : ℂ) + Complex.cosh ((a : ℂ) * z) = 0 ∧ z.re ≠ 0}

end MathlibPlus.Open.Analysis
