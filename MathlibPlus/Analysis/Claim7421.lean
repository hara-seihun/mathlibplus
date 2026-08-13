import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- Claim 7421: the reciprocal kernel is a positive hyperbolic-cosine form. -/
theorem claim7421_reciprocalKernel (a q t : ℝ) :
    let c : ℝ := Real.cosh t
    let s : ℝ := Real.sinh t
    let z : ℝ := a * t - q * s
    let K : ℝ := Real.exp (-a * t - q * Real.exp (-t)) +
      Real.exp (a * t - q * Real.exp t)
    K = 2 * Real.exp (-q * c) * Real.cosh z ∧ 0 < K := by
  dsimp
  have hminus : Real.exp (-t) = Real.cosh t - Real.sinh t := by
    rw [Real.cosh_eq, Real.sinh_eq]
    rw [Real.exp_neg]
    ring
  have hplus : Real.exp t = Real.cosh t + Real.sinh t := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hleft : -a * t - q * Real.exp (-t) =
      -q * Real.cosh t - (a * t - q * Real.sinh t) := by
    rw [hminus]
    ring
  have hright : a * t - q * Real.exp t =
      -q * Real.cosh t + (a * t - q * Real.sinh t) := by
    rw [hplus]
    ring
  have he1 : Real.exp (-q * Real.cosh t - (a * t - q * Real.sinh t)) =
      Real.exp (-q * Real.cosh t) * Real.exp (-(a * t - q * Real.sinh t)) := by
    rw [show -q * Real.cosh t - (a * t - q * Real.sinh t) =
      (-q * Real.cosh t) + (-(a * t - q * Real.sinh t)) by ring, Real.exp_add]
  have he2 : Real.exp (-q * Real.cosh t + (a * t - q * Real.sinh t)) =
      Real.exp (-q * Real.cosh t) * Real.exp (a * t - q * Real.sinh t) := by
    rw [Real.exp_add]
  have hcoshz : Real.cosh (a * t - q * Real.sinh t) =
      (Real.exp (a * t - q * Real.sinh t) +
        Real.exp (-(a * t - q * Real.sinh t))) / 2 := by
    rw [Real.cosh_eq]
  constructor
  · rw [hleft, hright, he1, he2, hcoshz]
    ring
  · positivity

end MathlibPlus.Analysis
