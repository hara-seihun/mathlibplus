import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 17955.  Center/relative coordinates for two shell logarithmic
variables, including the shifted relative coordinate and the inverse identities.
The positivity hypotheses retain the source domain of the shell indices.
-/
theorem centerRelativeCoordinates_claim17955
    (u v : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let c := (u + v) / 2
    let d := (u - v) / 2
    let r := d + (1 / 2 : ℝ) * Real.log ((m : ℝ) / (n : ℝ))
    c + d = u ∧ c - d = v ∧
      2 * r = (u - v) + Real.log ((m : ℝ) / (n : ℝ)) := by
  dsimp
  constructor
  · ring
  constructor <;> ring

/--
Claim 17956.  Exact hyperbolic identity for the two positive shells, using the
center/relative coordinates of claim 17955.
-/
theorem twoShellHyperbolicIdentity_claim17956
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (u v : ℝ) :
    let c := (u + v) / 2
    let d := (u - v) / 2
    let r := d + (1 / 2 : ℝ) * Real.log ((m : ℝ) / (n : ℝ))
    let x := Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u)
    let y := Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * v)
    x + y =
      2 * Real.pi * (m : ℝ) * (n : ℝ) * Real.exp (2 * c) * Real.cosh (2 * r) := by
  dsimp
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmn : (0 : ℝ) < (m : ℝ) / (n : ℝ) := div_pos hm' hn'
  have hc : 2 * ((u + v) / 2) = u + v := by ring
  have hr : 2 * ((u - v) / 2 + (1 / 2 : ℝ) * Real.log ((m : ℝ) / (n : ℝ))) =
      (u - v) + Real.log ((m : ℝ) / (n : ℝ)) := by ring
  rw [Real.cosh_eq, hc, hr]
  have houter : Real.exp (u + v) = Real.exp u * Real.exp v := by
    rw [Real.exp_add]
  have hinner :
      Real.exp (u - v + Real.log ((m : ℝ) / (n : ℝ))) =
        Real.exp (u - v) * ((m : ℝ) / (n : ℝ)) := by
    rw [Real.exp_add, Real.exp_log hmn]
  have hinner_neg :
      Real.exp (-(u - v + Real.log ((m : ℝ) / (n : ℝ)))) =
        (Real.exp (u - v) * ((m : ℝ) / (n : ℝ)))⁻¹ := by
    rw [Real.exp_neg, hinner]
  rw [houter, hinner, hinner_neg]
  have hsub : Real.exp (u - v) = Real.exp u / Real.exp v := by
    rw [Real.exp_sub]
  have h2u : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [show 2 * u = u + u by ring, Real.exp_add]
  have h2v : Real.exp (2 * v) = Real.exp v * Real.exp v := by
    rw [show 2 * v = v + v by ring, Real.exp_add]
  rw [hsub, h2u, h2v]
  field_simp [Real.exp_ne_zero]

end MathlibPlus.Algebra
