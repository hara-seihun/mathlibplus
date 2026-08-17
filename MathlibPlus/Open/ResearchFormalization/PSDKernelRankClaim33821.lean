import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.PSDKernelRankClaim33821

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


/-- The three infinitesimal similarity vectors in the planar cyclic carrier. -/
def kernelOne (m : ℕ) : Fin m → ℝ := fun _ => 1

def kernelCos (m : ℕ) : Fin m → ℝ :=
  fun j => Real.cos (2 * Real.pi * (j.val : ℝ) / m)

def kernelSin (m : ℕ) : Fin m → ℝ :=
  fun j => Real.sin (2 * Real.pi * (j.val : ℝ) / m)

/-- Claim 33821: exact mode signs, the elementary strict sine bound, and the
PSD/kernel/rank statement for the actual signed stress matrix. -/
def claim33821 : Prop :=
  ∀ (m : ℕ), 7 ≤ m → Odd m →
    let k := (m - 1) / 2
    let x := regularPolygon m
    let D := planarDiameter x
    let a := Real.pi / (2 * (m : ℝ))
    let Ω := signedStress m k D
    (∀ r : ℕ, r < m →
      (stressEigenvalue m k r D = 0 ↔
        r = 0 ∨ r = 1 ∨ r = m - 1)) ∧
    (∀ r : ℕ, 2 ≤ r → r ≤ m - 2 →
      |Real.sin (Real.pi * (r : ℝ) / m)| ≥ Real.sin (4 * a) ∧
      Real.sin (4 * a) > 2 * Real.sin a ∧
      0 < stressEigenvalue m k r D) ∧
    Real.pi < 22 / 7 ∧
    a < 11 / 49 ∧
    2 * Real.cos a * Real.cos (2 * a) > 1 ∧
    Matrix.PosSemidef Ω ∧
    LinearMap.ker (Matrix.mulVecLin Ω) =
      Submodule.span ℝ
        ({kernelOne m, kernelCos m, kernelSin m} : Set (Fin m → ℝ)) ∧
    Matrix.rank Ω = m - 3

end
end MathlibPlus.Open.ResearchFormalization.PSDKernelRankClaim33821
