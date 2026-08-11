import Mathlib

/-!
# Reciprocal xi transform and oriented Hankel flag

Definitions from admitted claim 375.  The entire Riemann xi function is written
using mathlib's pole-removed `completedRiemannZeta₀`; the identity
`ξ(s) = (1 + s(s-1) Λ₀(s)) / 2` avoids totalization artifacts at `s = 0, 1`.
-/

open MeasureTheory Matrix

namespace MathlibPlus.Analysis.ReciprocalXi

/-- Riemann's entire xi function in terms of mathlib's pole-removed completed zeta. -/
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- The centered entire function `X(z) = ξ(1/2 + z)`. -/
noncomputable def centeredXi (z : ℂ) : ℂ :=
  xi ((1 / 2 : ℂ) + z)

/-- The reciprocal-xi Fourier transform
`F(t) = ∫_ℝ exp(i t x) / X(x) dx`. -/
noncomputable def transform (t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) / centeredXi (x : ℂ)

/-- The normalization `Λ(t) = F(t) / (2π)`. -/
noncomputable def lambdaTransform (t : ℝ) : ℂ :=
  transform t / (2 * (Real.pi : ℂ))

/-- The oriented derivative-Hankel flag
`H_m(t) = (-1)^(m(m-1)/2) det [F^(i+j)(t)]`. -/
noncomputable def orientedHankelFlag (m : ℕ) (t : ℝ) : ℂ :=
  (-1 : ℂ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m =>
      iteratedDeriv (i.val + j.val) transform t)

/-- The empty oriented Hankel determinant is one, as required by `H₀ = 1`. -/
@[simp] theorem orientedHankelFlag_zero (t : ℝ) : orientedHankelFlag 0 t = 1 := by
  unfold orientedHankelFlag
  let A : Matrix (Fin 0) (Fin 0) ℂ := fun i j =>
    iteratedDeriv (i.val + j.val) transform t
  change (-1 : ℂ) ^ (0 * (0 - 1) / 2) * Matrix.det A = 1
  rw [Matrix.det_isEmpty]
  norm_num

end MathlibPlus.Analysis.ReciprocalXi
