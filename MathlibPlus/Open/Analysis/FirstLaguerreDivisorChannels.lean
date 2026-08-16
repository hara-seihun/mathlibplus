import MathlibPlus.Analysis.ReciprocalXi

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.FirstLaguerreDivisorChannels

noncomputable section

/-- The primitive completed-theta shell `f_n`. -/
def thetaPrimitiveShell (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)))

/-- The literal completed-theta shell
`φ_n = (∂ᵤ² - 1/4) f_n`. -/
def completedThetaShell (n : ℕ) (u : ℝ) : ℝ :=
  iteratedDeriv 2 (thetaPrimitiveShell n) u -
    (1 / 4 : ℝ) * thetaPrimitiveShell n u

/-- The completed-theta source `Φ = ∑_{n ≥ 1} φ_n`. -/
noncomputable def completedThetaSource (u : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 1 ≤ n}, completedThetaShell n.1 u

/-- The source channel consisting of shells with `q ∣ n`. -/
noncomputable def qDivisibleThetaSource (q : ℕ) (u : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 1 ≤ n ∧ q ∣ n}, completedThetaShell n.1 u

/-- The complementary source channel consisting of shells with `q ∤ n`. -/
noncomputable def qNondivisibleThetaSource (q : ℕ) (u : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 1 ≤ n ∧ ¬q ∣ n}, completedThetaShell n.1 u

/-- The two exact shell channels, indexed by `0 = q ∣ n` and
`1 = q ∤ n`. -/
noncomputable def channelSource (q : ℕ) (i : Fin 2) (u : ℝ) : ℝ :=
  if i = (0 : Fin 2) then
    qDivisibleThetaSource q u
  else
    qNondivisibleThetaSource q u

/-- The completed-xi carrier fixed by the packet:
`X(x) = ξ(1/2 + i x)`. -/
noncomputable def completedXiOnCriticalLine (x : ℝ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + Complex.I * (x : ℂ))

/-- The divisor multiplier
`a_q(x) = q^(-1/2) exp(-i x log q)`. -/
noncomputable def divisorMultiplier (q : ℕ) (x : ℝ) : ℂ :=
  (Real.rpow (q : ℝ) (-1 / 2 : ℝ) : ℂ) *
    Complex.exp
      (-Complex.I * (x : ℂ) * (Real.log (q : ℝ) : ℂ))

/-- The positive-phase Fourier transform used by the shell identities. -/
noncomputable def thetaFourier (f : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ u : ℝ,
    Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) * (f u : ℂ)

/-- The Fourier transform of an exact divisor/complement shell channel. -/
noncomputable def channelTransform (q : ℕ) (i : Fin 2) (x : ℝ) : ℂ :=
  thetaFourier (channelSource q i) x

/-- The closed-form transforms supplied by the divisor/complement split. -/
noncomputable def divisorComplementTransform
    (q : ℕ) (i : Fin 2) (x : ℝ) : ℂ :=
  if i = (0 : Fin 2) then
    divisorMultiplier q x * completedXiOnCriticalLine x
  else
    (1 - divisorMultiplier q x) * completedXiOnCriticalLine x

/-- The literal first-Laguerre two-copy kernel.  The squared integration
coordinate is part of the kernel. -/
noncomputable def channelKernel
    (q : ℕ) (i j : Fin 2) (y : ℝ) : ℝ :=
  ∫ d : ℝ,
    d ^ 2 * channelSource q i (d - y) * channelSource q j (d + y)

/-- The literal zero-heat first-Laguerre covariance `J₀` of the complete
completed-theta source. -/
noncomputable def zeroHeatFirstLaguerreCovariance (y : ℝ) : ℝ :=
  ∫ d : ℝ,
    d ^ 2 * completedThetaSource (d - y) * completedThetaSource (d + y)

/-- The Fourier transform of a real-side channel kernel, with the packet's
`exp(2 i x y)` Fourier phase. -/
noncomputable def channelKernelFourier
    (q : ℕ) (i j : Fin 2) (x : ℝ) : ℂ :=
  ∫ y : ℝ,
    Complex.exp (2 * Complex.I * ((y * x : ℝ) : ℂ)) *
      (channelKernel q i j y : ℂ)

/-- The exact first-Laguerre Fourier entry associated with two complex
channel transforms. -/
noncomputable def firstLaguerreFourierEntry
    (F G : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / 8 : ℂ) *
    (2 * star (deriv F x) * deriv G x -
      star (iteratedDeriv 2 F x) * G x -
      star (F x) * iteratedDeriv 2 G x)

/-- The Fourier matrix `K̂` of the literal channel kernels. -/
noncomputable def channelFourierMatrix
    (q : ℕ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => channelKernelFourier q i j x

/-- The exact Hermitian first-Laguerre matrix formula for the channel
transforms. -/
noncomputable def firstLaguerreFourierMatrix
    (q : ℕ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    firstLaguerreFourierEntry
      (channelTransform q i) (channelTransform q j) x

/-- The exact transform identity for the two shell channels. -/
def channelTransformAgreement (q : ℕ) : Prop :=
  ∀ (i : Fin 2) (x : ℝ),
    channelTransform q i x = divisorComplementTransform q i x

/-- The exact identification of the Fourier transform of the literal
kernels with the Hermitian derivative matrix. -/
def channelMatrixAgreement (q : ℕ) : Prop :=
  ∀ (i j : Fin 2) (x : ℝ),
    channelFourierMatrix q x i j = firstLaguerreFourierMatrix q x i j

/-- Positive semidefiniteness for the complex Hermitian channel matrix. -/
def complexMatrixPosSemidefinite
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M.IsHermitian ∧
    ∀ v : Fin 2 → ℂ,
      0 ≤
        (∑ i : Fin 2, ∑ j : Fin 2,
          star (v i) * M i j * v j).re

/-- The scalar Fourier-side first-Laguerre expression. -/
noncomputable def scalarFirstLaguerreFourier (x : ℝ) : ℂ :=
  (1 / 4 : ℂ) *
    (deriv completedXiOnCriticalLine x ^ 2 -
      completedXiOnCriticalLine x *
        iteratedDeriv 2 completedXiOnCriticalLine x)

/-- The normalized curvature used in the determinant identity. -/
noncomputable def logarithmicCurvature (x : ℝ) : ℂ :=
  (deriv completedXiOnCriticalLine x ^ 2 -
      completedXiOnCriticalLine x *
        iteratedDeriv 2 completedXiOnCriticalLine x) /
    completedXiOnCriticalLine x ^ 2

/-- Claim 15058: the four exact divisor/complement kernels recover the
literal scalar covariance, their Fourier matrix has the scalar all-ones
quadratic form, and matrix positive semidefiniteness implies scalar
first-Laguerre positivity. -/
def claim15058 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    channelTransformAgreement q ∧
      channelMatrixAgreement q ∧
        (∀ y : ℝ,
          (∑ i : Fin 2, ∑ j : Fin 2, channelKernel q i j y) =
            zeroHeatFirstLaguerreCovariance y) ∧
          (∀ x : ℝ,
            (∑ i : Fin 2, ∑ j : Fin 2, channelFourierMatrix q x i j) =
              scalarFirstLaguerreFourier x) ∧
            (∀ x : ℝ,
              complexMatrixPosSemidefinite (channelFourierMatrix q x) →
                0 ≤ (scalarFirstLaguerreFourier x).re)

/-- Claim 15059: wherever the fixed completed-xi carrier is nonzero, the
exact divisor/complement Fourier matrix has the stated determinant. -/
def claim15059 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    channelTransformAgreement q ∧
      channelMatrixAgreement q ∧
        ∀ x : ℝ, completedXiOnCriticalLine x ≠ 0 →
          Matrix.det (channelFourierMatrix q x) =
            completedXiOnCriticalLine x ^ 4 *
                (Real.log (q : ℝ) : ℂ) ^ 2 *
                (Complex.normSq (divisorMultiplier q x) : ℂ) *
              (4 * logarithmicCurvature x -
                (Real.log (q : ℝ) : ℂ) ^ 2) / 64

end

end MathlibPlus.Open.Analysis.FirstLaguerreDivisorChannels
