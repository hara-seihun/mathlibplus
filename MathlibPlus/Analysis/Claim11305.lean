import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim11305

/-!
The source's geometric labels are not defined by a shared Lean API.  This file
retains its exact arithmetic frame: the eight-zero count split, the two line
samples, the displayed complex witness, and the degree-one rejection rule.
-/

noncomputable def witnessPolynomial (z : ℂ) : ℂ := z * (z - 1 / 2)

noncomputable def witnessPoint : ℂ := (153 + 54 * Complex.I) / 325

def degreeOneCandidate (c z : ℂ) : ℂ := c * z

theorem lineSamples_annihilated :
    witnessPolynomial 0 = 0 ∧ witnessPolynomial (1 / 2) = 0 := by
  norm_num [witnessPolynomial]

theorem witnessSigns :
    4 * (witnessPolynomial witnessPoint ^ 2).re =
        -(163817883 : ℝ) / 11156640625 ∧
      4 * (witnessPolynomial witnessPoint).im ^ 2 =
        (240188004 : ℝ) / 11156640625 ∧
      (0 : ℝ) < (240188004 : ℝ) / 11156640625 := by
  norm_num [witnessPolynomial, witnessPoint, pow_two, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.div_re,
    Complex.div_im]

theorem degreeOne_positive_sample_rejected
    (c : ℂ) (hc : c ≠ 0) (x : ℝ) (hx : 0 < x) :
    degreeOneCandidate c (x : ℂ) ≠ 0 := by
  apply mul_ne_zero hc
  exact_mod_cast (ne_of_gt hx)

/-- The exact arithmetic countercertificate recorded in claim 11305. -/
theorem smallestExactCountOnlyFrame_claim11305 :
    (4 : ℚ) / 8 = 1 / 2 ∧
    witnessPolynomial 0 = 0 ∧
    witnessPolynomial (1 / 2) = 0 ∧
    4 * (witnessPolynomial witnessPoint ^ 2).re =
      -(163817883 : ℝ) / 11156640625 ∧
    4 * (witnessPolynomial witnessPoint).im ^ 2 =
      (240188004 : ℝ) / 11156640625 ∧
    (0 : ℝ) < (240188004 : ℝ) / 11156640625 ∧
    (∀ c : ℂ, c ≠ 0 → ∀ x : ℝ, 0 < x →
      degreeOneCandidate c (x : ℂ) ≠ 0) := by
  refine ⟨by norm_num, lineSamples_annihilated.1,
    lineSamples_annihilated.2, witnessSigns.1, witnessSigns.2.1,
    witnessSigns.2.2, ?_⟩
  intro c hc x hx
  exact degreeOne_positive_sample_rejected c hc x hx

end MathlibPlus.Analysis.Claim11305
