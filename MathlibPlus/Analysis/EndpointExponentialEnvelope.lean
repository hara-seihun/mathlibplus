import Mathlib

namespace MathlibPlus.Analysis

/-- Endpoint exponential envelope for the reflected cosine packet. -/
theorem claim11210_endpointExponentialEnvelope
    (L t η x : ℝ) (hη : 0 ≤ η) (hx0 : 0 ≤ x) (hx2L : x ≤ 2 * L) :
    let z : ℂ := (t : ℂ) + (η : ℂ) * Complex.I
    ‖2 * Complex.exp (Complex.I * (L : ℂ) * z) *
        Complex.cos (z * ((x - L : ℝ) : ℂ))‖ ≤
      Real.exp (-η * x) + Real.exp (-η * (2 * L - x)) := by
  dsimp
  have hcos (a w : ℂ) :
      2 * Complex.exp a * Complex.cos w =
        Complex.exp (a + w * Complex.I) +
          Complex.exp (a + (-w) * Complex.I) := by
    rw [Complex.cos]
    calc
      2 * Complex.exp a *
          ((Complex.exp (w * Complex.I) +
            Complex.exp (-w * Complex.I)) / 2) =
          Complex.exp a * Complex.exp (w * Complex.I) +
            Complex.exp a * Complex.exp (-w * Complex.I) := by ring
      _ = Complex.exp (a + w * Complex.I) +
            Complex.exp (a + (-w) * Complex.I) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
  rw [hcos]
  have hexp :
      Complex.I * (L : ℂ) * ((t : ℂ) + (η : ℂ) * Complex.I) +
          (((t : ℂ) + (η : ℂ) * Complex.I) * ((x - L : ℝ) : ℂ)) * Complex.I =
        Complex.I * ((t : ℂ) + (η : ℂ) * Complex.I) * (x : ℂ) := by
    push_cast
    ring
  have hexp' :
      Complex.I * (L : ℂ) * ((t : ℂ) + (η : ℂ) * Complex.I) +
          (-(((t : ℂ) + (η : ℂ) * Complex.I) * ((x - L : ℝ) : ℂ))) * Complex.I =
        Complex.I * ((t : ℂ) + (η : ℂ) * Complex.I) *
          ((2 * L - x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, hexp']
  calc
    ‖Complex.exp (Complex.I * ((t : ℂ) + (η : ℂ) * Complex.I) * (x : ℂ)) +
          Complex.exp (Complex.I * ((t : ℂ) + (η : ℂ) * Complex.I) *
            ((2 * L - x : ℝ) : ℂ))‖ ≤
        ‖Complex.exp (Complex.I * ((t : ℂ) + (η : ℂ) * Complex.I) * (x : ℂ))‖ +
          ‖Complex.exp (Complex.I * ((t : ℂ) + (η : ℂ) * Complex.I) *
            ((2 * L - x : ℝ) : ℂ))‖ := norm_add_le _ _
    _ = Real.exp (-η * x) + Real.exp (-η * (2 * L - x)) := by
      rw [Complex.norm_exp, Complex.norm_exp]
      congr 1 <;> simp [Complex.mul_re, Complex.add_re, Complex.I_re,
        Complex.I_im]

end MathlibPlus.Analysis
