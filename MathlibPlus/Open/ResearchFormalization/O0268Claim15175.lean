import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatch
import MathlibPlus.Analysis.ReciprocalXi

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0268Claim15175

noncomputable section

private def admissibleProfile
    (k : ℕ) (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ) : Prop :=
  1 ≤ k ∧
    (∀ L : ℝ, 1 ≤ B L) ∧
    (∀ L : ℝ,
      P L = 1 + ∑ j ∈ Finset.Icc 1 (d L),
        Polynomial.monomial j (coeff L j)) ∧
    (∀ (L : ℝ) (j : ℕ), j ∈ Finset.Icc 1 (d L) →
      ‖coeff L j‖ ≤ (B L) ^ j) ∧
    Tendsto (fun L : ℝ => (B L) ^ k * (d L : ℝ) / L)
      atTop (𝓝 0) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ) * Real.log (B L))
      (fun L : ℝ => L)

private noncomputable def xiPlane (z : ℂ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + Complex.I * z)

private noncomputable def profileValue
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  (P L).eval
    (z ^ 2 / (Real.rpow L (1 / (k : ℝ)) : ℂ))

private noncomputable def profileCarrier
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  xiPlane z / (2 * (Real.pi : ℂ)) * profileValue P k L z

private noncomputable def diniCarrier (L : ℝ) (z : ℂ) : ℂ :=
  (z * Complex.sin ((L : ℂ) * z) -
      (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 + (1 / 4 : ℂ))

private noncomputable def ghatCarrier (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (L : ℂ) * z) * diniCarrier L z

private noncomputable def actionConstant
    (amplification : ℝ → ℝ) (L : ℝ) : ℝ :=
  MathlibPlus.Open.Analysis.FormalizationBatch.movingActionConstant
    amplification L

private noncomputable def transitionScale (k : ℕ) (L : ℝ) : ℝ :=
  Real.rpow L (1 / (2 * (k : ℝ)))

private noncomputable def movingKappa
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (L y : ℝ) : ℝ :=
  Real.rpow
    ((actionConstant amplification L - y) / alpha)
    (1 / (2 * (k : ℝ)))

private noncomputable def graphPoint
    (k : ℕ) (kappa y L : ℝ) : ℂ :=
  (kappa * transitionScale k L : ℂ) +
    (y : ℂ) * Complex.I

private noncomputable def leadingAction
    (k : ℕ) (alpha A L : ℝ) (z : ℂ) : ℂ :=
  (alpha : ℂ) * z ^ (2 * k) -
    Complex.I * (L : ℂ) * z - ((A * L : ℝ) : ℂ)

private noncomputable def logarithmicCoordinate
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  leadingAction k alpha (actionConstant amplification L) L z -
    Complex.log (profileCarrier P k L z / ghatCarrier L z)

/-- Claim 15175: with the exact Xi/Dini logarithmic-coordinate carriers, the
moving leading action has the positive zero-action graph and point-dependent
`o(L)` errors on the fixed compact supplied by item 2. -/
def claim15175 : Prop :=
  ∀ (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ)
    (y₀ y₁ : ℝ),
    admissibleProfile k P d B coeff →
      0 < alpha →
      (∀ L : ℝ, 1 ≤ amplification L) →
      Tendsto (fun L : ℝ => amplification L * Real.exp (-2 * L))
        atTop (𝓝 0) →
      0 < y₀ → y₀ < y₁ → y₁ < (1 : ℝ) / 2 →
      MathlibPlus.Open.Analysis.FormalizationBatch.movingActionConstantBounds
        amplification y₀ y₁ →
      let q : ℝ := 1 / (2 * (k : ℝ))
      let kappa : ℝ → ℝ → ℝ := fun L y =>
        Real.rpow ((actionConstant amplification L - y) / alpha) q
      ∃ c C : ℝ,
        0 < c ∧ c < C ∧
        (∀ᶠ L : ℝ in atTop,
          ∀ y ∈ Set.Icc y₀ y₁,
            c ≤ kappa L y ∧ kappa L y ≤ C) ∧
        (∀ᶠ L : ℝ in atTop,
          ∀ y ∈ Set.Icc y₀ y₁,
            0 < actionConstant amplification L - y ∧
            alpha * (kappa L y) ^ (2 * k) + y -
                actionConstant amplification L = 0 ∧
            (∀ kappaValue : ℝ, 0 < kappaValue →
              (alpha * kappaValue ^ (2 * k) + y -
                    actionConstant amplification L = 0 ↔
                kappaValue = kappa L y))) ∧
        (∀ kappaValue ∈ Set.Icc c C,
          ∀ y ∈ Set.Icc y₀ y₁,
            ∃ error : ℝ → ℝ,
              Tendsto error atTop (𝓝 0) ∧
                ∀ᶠ L : ℝ in atTop,
                  (profileCarrier P k L
                      (graphPoint k kappaValue y L) ≠ 0 ∧
                    ghatCarrier L
                      (graphPoint k kappaValue y L) ≠ 0 →
                    (logarithmicCoordinate k alpha amplification P L
                        (graphPoint k kappaValue y L)).re =
                      L * (alpha * kappaValue ^ (2 * k) + y -
                          actionConstant amplification L) +
                        L * error L))

end

end MathlibPlus.Open.ResearchFormalization.O0268Claim15175
