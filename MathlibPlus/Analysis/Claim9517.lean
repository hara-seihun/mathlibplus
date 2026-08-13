import Mathlib

namespace MathlibPlus.Analysis.Claim9517

/-- Claim 9517: the exponential kernel is annihilated by the first-order
operator `∂ + φ'`. -/
theorem kernel_identity (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    let h : ℝ → ℝ := fun x => Real.exp (-φ x)
    let L : (ℝ → ℝ) → (ℝ → ℝ) :=
      fun f x => deriv f x + deriv φ x * f x
    ∀ x, L h x = 0 := by
  dsimp
  intro x
  have hφx : HasDerivAt φ (deriv φ x) x :=
    (hφ.differentiableAt).hasDerivAt
  have hneg : HasDerivAt (-φ) (-deriv φ x) x := hφx.neg
  have hexp : HasDerivAt (fun y => Real.exp (-φ y))
      (Real.exp (-φ x) * (-deriv φ x)) x := by
    simpa only [Pi.neg_apply] using hneg.exp
  rw [hexp.deriv]
  ring

end MathlibPlus.Analysis.Claim9517
