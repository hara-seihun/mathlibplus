import Mathlib

namespace MathlibPlus.Analysis.Claim2484

/-- An entire function that is real on the real axis. -/
def RealEntire (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ x : ℝ, (F x).im = 0

/-- The real-linear correction family in the packet. -/
def realEntireCorrection (F₀ C : ℂ → ℂ) (s : ℝ) : ℂ → ℂ :=
  fun z => F₀ z + (s : ℂ) * C z

/-- A real linear combination of real-entire functions is real-entire, and its
pointwise formula is the stated `F_s(z)=F₀(z)+sC(z)`. -/
theorem real_linear_entire_homotopy_claim2484
    (F₀ C : ℂ → ℂ) (hF₀ : RealEntire F₀) (hC : RealEntire C) (s : ℝ) :
    RealEntire (realEntireCorrection F₀ C s) ∧
      ∀ z, realEntireCorrection F₀ C s z = F₀ z + (s : ℂ) * C z := by
  constructor
  · constructor
    · exact hF₀.1.add (hC.1.const_mul (s : ℂ))
    · intro x
      change (F₀ (x : ℂ) + (s : ℂ) * C (x : ℂ)).im = 0
      simp [Complex.add_im, Complex.mul_im, hF₀.2 x, hC.2 x]
  · intro z
    rfl

end MathlibPlus.Analysis.Claim2484
