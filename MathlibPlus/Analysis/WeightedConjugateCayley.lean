import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The reciprocal map on positive reals is involutive. -/
theorem reciprocalPositiveInvolutive_claim4868 (x : Set.Ioi (0 : ℝ)) :
    ((x.1)⁻¹)⁻¹ = x.1 := by
  simp

/-- The weighted conjugation from the Weil reflection data is an involution.
The compact-support and smoothness conditions are irrelevant to this algebraic
identity, so the statement is made for all complex-valued functions on the
positive reals. -/
theorem weightedConjugateInvolutive_claim4868 :
    let sharp : (Set.Ioi (0 : ℝ) → ℂ) → (Set.Ioi (0 : ℝ) → ℂ) := fun f x =>
      (x.1 : ℂ)⁻¹ * (starRingEnd ℂ) (f ⟨x.1⁻¹, by
        change 0 < x.1⁻¹
        exact inv_pos.mpr x.2⟩)
    ∀ f, sharp (sharp f) = f := by
  dsimp
  intro f
  funext x
  simp only [map_mul, starRingEnd_apply, Complex.ofReal_inv, star_star,
    inv_inv]
  have hstar : star (x.1 : ℂ) = (x.1 : ℂ) := by
    change (starRingEnd ℂ) (x.1 : ℂ) = (x.1 : ℂ)
    exact Complex.conj_ofReal x.1
  rw [hstar]
  simp only [Subtype.coe_eta]
  have hx0 : (x.1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt x.2)
  rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

/-- A critical-line Cayley mode `b = 1/(rho-1)` satisfies the exact
quadratic relation used by the exterior-square calculation. -/
theorem criticalLineCayleyModeIdentity_claim15674 (γ : ℝ) :
    let b : ℂ := 1 / (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I - 1)
    2 * b.re + Complex.normSq b = 0 := by
  dsimp
  let z : ℂ := (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I - 1)
  have hzre : z.re = -(1 / 2 : ℝ) := by
    dsimp [z]
    norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hzim : z.im = γ := by
    dsimp [z]
    norm_num [Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hzns : Complex.normSq z = (1 / 2 : ℝ) ^ 2 + γ ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  change 2 * (1 / z).re + Complex.normSq (1 / z) = 0
  simp only [one_div]
  change 2 * (z⁻¹).re + Complex.normSq (z⁻¹) = 0
  rw [Complex.inv_re, Complex.normSq_inv, hzre, hzns]
  field_simp; ring

end MathlibPlus.Analysis
