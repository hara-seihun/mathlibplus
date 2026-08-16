import MathlibPlus.Analysis.ReciprocalXi

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FiniteDivisibilityFirstLaguerre

/-- The completed-theta shell body used by the cumulative channels. -/
noncomputable def shellBody (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))

/-- The literal first-Laguerre shell `((∂²) - 1/4) f_n`. -/
noncomputable def shell (n : ℕ) (u : ℝ) : ℝ :=
  iteratedDeriv 2 (shellBody n) u - (1 / 4 : ℝ) * shellBody n u

/-- The q-divisible completed-theta shell channel, with the source sum over
positive indices represented by `n + 1`. -/
noncomputable def cumulativeShell (q : ℕ) (u : ℝ) : ℝ :=
  ∑' n : ℕ, if q ∣ (n + 1) then shell (n + 1) u else 0

/-- The unnormalised Fourier transform of the literal cumulative channel. -/
noncomputable def cumulativeFourier (q : ℕ) (x : ℝ) : ℂ :=
  ∫ u : ℝ,
    Complex.exp (-Complex.I * ((u * x : ℝ) : ℂ)) *
      (cumulativeShell q u : ℂ)

/-- The existing pole-removed completed-xi carrier on the critical line. -/
noncomputable def centeredXiAxis (x : ℝ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)

/-- The body-defined normalized second derivative at the center. -/
noncomputable def centralXiCurvature : ℂ :=
  iteratedDeriv 2 MathlibPlus.Analysis.ReciprocalXi.xi (1 / 2 : ℂ) /
    MathlibPlus.Analysis.ReciprocalXi.xi (1 / 2 : ℂ)

/-- The Hermitian first-Laguerre Fourier contraction of two literal channels. -/
noncomputable def firstLaguerreEntry (q r : ℕ) (x : ℝ) : ℂ :=
  (1 / 8 : ℂ) *
    (2 * starRingEnd ℂ (iteratedDeriv 1 (cumulativeFourier q) x) *
        iteratedDeriv 1 (cumulativeFourier r) x -
      starRingEnd ℂ (iteratedDeriv 2 (cumulativeFourier q) x) *
        cumulativeFourier r x -
      starRingEnd ℂ (cumulativeFourier q x) *
        iteratedDeriv 2 (cumulativeFourier r) x)

/-- The pair matrix indexed by the two chosen cumulative channels. -/
noncomputable def pairMatrix (q r : ℕ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![firstLaguerreEntry q q x, firstLaguerreEntry q r x;
    firstLaguerreEntry r q x, firstLaguerreEntry r r x]

/-- Claim 15147: the central entry formula for the literal cumulative
completed-theta channels. -/
def centralEntryFormula : Prop :=
  ∀ q r : ℕ, 0 < q → 0 < r →
    firstLaguerreEntry q r 0 =
      let X₀ := centeredXiAxis 0
      let ℓ₀ := centralXiCurvature
      let Lq : ℂ := (Real.log (q : ℝ) : ℂ)
      let Lr : ℂ := (Real.log (r : ℝ) : ℂ)
      X₀ ^ 2 /
          ((8 : ℂ) * (Real.sqrt ((q : ℝ) * (r : ℝ)) : ℂ)) *
        ((Lq + Lr) ^ 2 + 2 * ℓ₀)

/-- Claim 15148: the exact determinant of the central pair matrix. -/
def centralPairDeterminant : Prop :=
  ∀ q r : ℕ, 0 < q → 0 < r →
    Matrix.det (pairMatrix q r 0) =
      let X₀ := centeredXiAxis 0
      let ℓ₀ := centralXiCurvature
      let Lq : ℂ := (Real.log (q : ℝ) : ℂ)
      let Lr : ℂ := (Real.log (r : ℝ) : ℂ)
      (-(X₀ ^ 4)) /
          ((64 : ℂ) * (q : ℂ) * (r : ℂ)) *
        (Lq - Lr) ^ 2 *
        (Lq ^ 2 + 6 * Lq * Lr + Lr ^ 2 - 4 * ℓ₀)

end MathlibPlus.Open.Analysis.FiniteDivisibilityFirstLaguerre
