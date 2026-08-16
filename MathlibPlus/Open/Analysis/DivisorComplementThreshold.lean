import MathlibPlus.Analysis.ReciprocalXi

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.DivisorComplementThreshold

/-- The completed-theta shell before applying the first Laguerre operator. -/
noncomputable def thetaPrimitiveShell (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)))

/-- The literal first-Laguerre shell
`(∂ᵤ² - 1/4) (exp(u/2) exp(-π n² exp(2u)))`. -/
noncomputable def completedThetaShell (n : ℕ) (u : ℝ) : ℝ :=
  deriv (fun v : ℝ => deriv (fun w : ℝ => thetaPrimitiveShell n w) v) u -
    (1 / 4 : ℝ) * thetaPrimitiveShell n u

/-- The completed-theta source, summed over the exact range `n ≥ 1`. -/
noncomputable def completedThetaSource (u : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 1 ≤ n}, completedThetaShell n.1 u

/-- The source channel containing exactly the shells with `q ∣ n`. -/
noncomputable def qDivisibleThetaSource (q : ℕ) (u : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 1 ≤ n ∧ q ∣ n}, completedThetaShell n.1 u

/-- The complementary source channel containing exactly the shells with `q ∤ n`. -/
noncomputable def qNondivisibleThetaSource (q : ℕ) (u : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 1 ≤ n ∧ ¬ q ∣ n}, completedThetaShell n.1 u

/-- The completed-theta transform fixed by the packet's normalization. -/
noncomputable def completedThetaTransform (x : ℝ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + Complex.I * (x : ℂ))

/-- The real critical-line restriction of the completed-theta transform `X`. -/
noncomputable def criticalXi (x : ℝ) : ℝ :=
  (completedThetaTransform x).re

/-- The divisor multiplier `a_q(x) = q^(-1/2) exp(-i x log q)`. -/
noncomputable def divisorMultiplier (q : ℕ) (x : ℝ) : ℂ :=
  (Real.rpow (q : ℝ) (-1 / 2 : ℝ) : ℂ) *
    Complex.exp
      (-Complex.I * (x : ℂ) * (Real.log (q : ℝ) : ℂ))

/-- The two exact shell-channel transforms, indexed by `0 = q ∣ n` and
`1 = q ∤ n`. -/
noncomputable def divisorComplementChannelTransform
    (q : ℕ) (i : Fin 2) (x : ℝ) : ℂ :=
  if i = (0 : Fin 2) then
    divisorMultiplier q x * (criticalXi x : ℂ)
  else
    (1 - divisorMultiplier q x) * (criticalXi x : ℂ)

/-- The first-Laguerre Fourier entry associated with two exact channel
transforms. -/
noncomputable def firstLaguerreFourierEntry
    (q : ℕ) (i j : Fin 2) (x : ℝ) : ℂ :=
  (1 / 8 : ℂ) *
    (2 * star (deriv (fun y : ℝ => divisorComplementChannelTransform q i y) x) *
        deriv (fun y : ℝ => divisorComplementChannelTransform q j y) x -
      star
          (deriv (fun y : ℝ =>
            deriv (fun z : ℝ => divisorComplementChannelTransform q i z) y) x) *
        divisorComplementChannelTransform q j x -
      star (divisorComplementChannelTransform q i x) *
        deriv (fun y : ℝ =>
          deriv (fun z : ℝ => divisorComplementChannelTransform q j z) y) x)

/-- The exact Hermitian two-by-two divisor/complement first-Laguerre matrix. -/
noncomputable def divisorComplementMatrix (q : ℕ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => firstLaguerreFourierEntry q i j x

/-- Positive semidefiniteness for the complex Hermitian matrix used by the
Fourier channels. -/
def complexMatrixPosSemidef
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M.IsHermitian ∧
    ∀ v : Fin 2 → ℂ,
      0 ≤ (∑ i, ∑ j, star (v i) * M i j * v j).re

/-- The scalar zero-heat first-Laguerre target at a point. -/
def scalarFirstLaguerreTarget (x : ℝ) : Prop :=
  0 ≤
    ((deriv criticalXi x) ^ 2 -
      criticalXi x * deriv (fun y : ℝ => deriv criticalXi y) x) /
      (criticalXi x) ^ 2

/-- The logarithmic curvature used in the threshold. -/
noncomputable def divisorComplementLogCurvature (x : ℝ) : ℝ :=
  ((deriv criticalXi x) ^ 2 -
      criticalXi x * deriv (fun y : ℝ => deriv criticalXi y) x) /
    (criticalXi x) ^ 2

/-- Claim 15060: positivity of the exact divisor/complement matrix forces the
stronger logarithmic threshold, which strictly strengthens the scalar target
for every integer `q ≥ 2`. -/
def claim15060_matrixPositivityThreshold : Prop :=
  (∀ (q : ℕ), 2 ≤ q →
    ∀ x : ℝ, criticalXi x ≠ 0 →
      complexMatrixPosSemidef (divisorComplementMatrix q x) →
        divisorComplementLogCurvature x ≥ (Real.log (q : ℝ)) ^ 2 / 4) ∧
  (∀ (q : ℕ), 2 ≤ q →
    0 < (Real.log (q : ℝ)) ^ 2 / 4 ∧
      ∀ x : ℝ,
        divisorComplementLogCurvature x ≥ (Real.log (q : ℝ)) ^ 2 / 4 →
          scalarFirstLaguerreTarget x)

end MathlibPlus.Open.Analysis.DivisorComplementThreshold
