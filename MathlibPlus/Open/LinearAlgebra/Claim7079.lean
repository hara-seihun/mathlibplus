import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

noncomputable section

open Matrix

abbrev CMat2 := Matrix (Fin 2) (Fin 2) ℂ

def flowDiagonal (a t : ℝ) : CMat2 :=
  !![(a : ℂ) + (t : ℂ) * Complex.I, 0;
     0, -(a : ℂ) + (t : ℂ) * Complex.I]

def hermitianForm (x y u w : ℝ) : CMat2 :=
  !![(x : ℂ), (y : ℂ) + (u : ℂ) * Complex.I;
     (y : ℂ) - (u : ℂ) * Complex.I, (w : ℂ)]

/-- The exact off-axis invariant-form classification and on-axis positive-form
assertion from the admitted flow statement. -/
def flowInvariantHermitianFormClaim7079 : Prop :=
  (∀ (a t x y u w : ℝ),
      a ≠ 0 →
        (flowDiagonal a t).conjTranspose * hermitianForm x y u w +
            hermitianForm x y u w * flowDiagonal a t = 0 →
        x = 0 ∧ w = 0 ∧
          Matrix.det (hermitianForm x y u w) =
            -((y ^ 2 + u ^ 2 : ℝ) : ℂ) ∧
          (hermitianForm x y u w ≠ 0 →
            (Matrix.det (hermitianForm x y u w)).re < 0)) ∧
    (∀ t : ℝ, ∃ P : CMat2,
      P.IsHermitian ∧
        (∀ v : Fin 2 → ℂ, v ≠ 0 →
          0 < (star v ⬝ᵥ (P *ᵥ v)).re) ∧
        (flowDiagonal 0 t).conjTranspose * P + P * flowDiagonal 0 t = 0)

end

end MathlibPlus.Open.LinearAlgebra
