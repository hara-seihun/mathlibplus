import Mathlib

namespace MathlibPlus.Algebra.Claim36744

/-- The constant-term consequence of the principal identity in claim 36744.
The parameter `z` is represented by `Polynomial.X`; all coefficients other than
its constant coefficient remain in the displayed identity. -/
theorem constantTerm_principal_identity {R : Type*} [CommRing R]
    (A B : Polynomial R) (g G x₁ s₁ s₂ : R)
    (hprincipal : A - B = Polynomial.C g *
      (Polynomial.C s₂ - Polynomial.X * Polynomial.C s₁))
    (hg : g = -G)
    (hB : B.coeff 0 = (x₁ * s₁ + s₂) * G) :
    A.coeff 0 - B.coeff 0 = g * s₂ ∧ A.coeff 0 = x₁ * s₁ * G := by
  have h0 : A.coeff 0 - B.coeff 0 = g * s₂ := by
    simpa using congrArg (fun P : Polynomial R => P.coeff 0) hprincipal
  refine ⟨h0, ?_⟩
  rw [hB, hg] at h0
  linear_combination h0

end MathlibPlus.Algebra.Claim36744
