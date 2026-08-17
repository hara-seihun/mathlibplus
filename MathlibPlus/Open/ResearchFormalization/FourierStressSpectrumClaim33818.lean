import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.FourierStressSpectrumClaim33818

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

/-- The real Laplacian of the step-`s` cycle on the cyclic vertex carrier. -/
def stepLaplacian (m s : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if i = j then 2
    else if Nat.ModEq m (i.val + s) j.val ∨
      Nat.ModEq m (j.val + s) i.val then -1
    else 0

/-- The signed contact-minus-diameter stress from the two actual cycle
Laplacians. -/
def signedStress (m k : ℕ) (D : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    (1 / (m : ℝ)) *
      (stepLaplacian m 1 i j - (1 / D ^ 2) * stepLaplacian m k i j)

/-- The cyclic complex Fourier vector, with the unnormalised mode convention. -/
def fourierMode (m r : ℕ) : Fin m → ℂ :=
  fun j =>
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        (((r : ℝ) * (j.val : ℝ) / (m : ℝ) : ℝ) : ℂ))

/-- The displayed stress eigenvalue. -/
def stressEigenvalue (m k r : ℕ) (D : ℝ) : ℝ :=
  (4 / (m : ℝ)) *
    (Real.sin (Real.pi * (r : ℝ) / m) ^ 2 -
      (1 / D ^ 2) * Real.sin (Real.pi * (k * r : ℕ) / m) ^ 2)

/-- Claim 33818: the regular-polygon diameter identity, the exact stress
Fourier spectrum, and the unscaled step-cycle Laplacian spectrum. -/
def claim33818 : Prop :=
  ∀ (m : ℕ), 7 ≤ m → Odd m →
    let k := (m - 1) / 2
    let x := regularPolygon m
    let D := planarDiameter x
    let a := Real.pi / (2 * (m : ℝ))
    let Ω := signedStress m k D
    (D = Real.sin (Real.pi * k / m) / Real.sin (Real.pi / m)) ∧
    (1 / D ^ 2 = 4 * Real.sin a ^ 2) ∧
    (∀ r : ℕ, r < m →
      stressEigenvalue m k r D =
        (4 / (m : ℝ)) *
          (Real.sin (Real.pi * (r : ℝ) / m) ^ 2 -
            4 * Real.sin a ^ 2 *
              Real.sin (Real.pi * (k * r : ℕ) / m) ^ 2)) ∧
    (∀ r : ℕ, r < m →
      Matrix.mulVec (Matrix.map Ω (algebraMap ℝ ℂ)) (fourierMode m r) =
        ((stressEigenvalue m k r D : ℂ) • fourierMode m r)) ∧
    (∀ s : ℕ, 1 ≤ s → s < m →
      ∀ r : ℕ, r < m →
        Matrix.mulVec
            (Matrix.map (stepLaplacian m s) (algebraMap ℝ ℂ))
            (fourierMode m r) =
          (((4 * Real.sin (Real.pi * (s : ℝ) * (r : ℝ) / m) ^ 2 : ℝ) : ℂ) •
            fourierMode m r))

end
end MathlibPlus.Open.ResearchFormalization.FourierStressSpectrumClaim33818
