import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatch
import MathlibPlus.Analysis.ReciprocalXi

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0268Claim15179

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
  MathlibPlus.Analysis.ReciprocalXi.xi ((1 / 2 : ℂ) + Complex.I * z)

private noncomputable def profileValue
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  (P L).eval (z ^ 2 / (Real.rpow L (1 / (k : ℝ)) : ℂ))

private noncomputable def profileCarrier
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  xiPlane z / (2 * (Real.pi : ℂ)) * profileValue P k L z

private noncomputable def diniCarrier (L : ℝ) (z : ℂ) : ℂ :=
  (z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 + (1 / 4 : ℂ))

private noncomputable def ghatCarrier (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (L : ℂ) * z) * diniCarrier L z

private noncomputable def modelFunction
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  profileCarrier P k L z * Complex.exp (-(alpha : ℂ) * z ^ (2 * k)) -
    (amplification L * Real.exp (-5 * L / 2) : ℂ) * diniCarrier L z

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

private noncomputable def movingRectangle
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (y₀ y₁ delta L : ℝ) : Set ℂ :=
  {z : ℂ |
    movingKappa k alpha amplification L y₁ * transitionScale k L ≤ z.re ∧
      z.re ≤ movingKappa k alpha amplification L y₀ * transitionScale k L ∧
      y₀ - 2 * delta ≤ z.im ∧ z.im ≤ y₁ + 2 * delta}

private noncomputable def zeroMultiplicity
    (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  if f z = 0 then (meromorphicOrderAt f z).untop₀.toNat else 0

private def countedZeroSet (f : ℂ → ℂ) (region : Set ℂ) : Set (ℂ × ℕ) :=
  {p | p.1 ∈ region ∧ p.2 < zeroMultiplicity f p.1}

private noncomputable def zeroCount (f : ℂ → ℂ) (region : Set ℂ) : ℕ :=
  (countedZeroSet f region).ncard

private noncomputable def actionWidth
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (L y₀ y₁ : ℝ) : ℝ :=
  (movingKappa k alpha amplification L y₀ -
    movingKappa k alpha amplification L y₁) / (2 * Real.pi)

/-- Claim 15179: the decreasing action-width calculation remains attached to
item 6's actual Xi-shadow/negative-Dini multiplicity count and gives the
uniform explicit alpha-normalized density floor. -/
def claim15179 : Prop :=
  ∀ (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ)
    (y₀ y₁ delta : ℝ),
    admissibleProfile k P d B coeff →
      0 < alpha →
      (∀ L : ℝ, 1 ≤ amplification L) →
      Tendsto (fun L : ℝ => amplification L * Real.exp (-2 * L))
        atTop (𝓝 0) →
      0 < y₀ → y₀ < y₁ → y₁ < (1 : ℝ) / 2 →
      0 < delta ∧ delta < (1 / 2 : ℝ) * min y₀ ((1 / 2 : ℝ) - y₁) →
      MathlibPlus.Open.Analysis.FormalizationBatch.movingActionConstantBounds
        amplification y₀ y₁ →
      let q : ℝ := 1 / (2 * (k : ℝ))
      let kappa : ℝ → ℝ → ℝ := fun L y =>
        Real.rpow ((actionConstant amplification L - y) / alpha) q
      let D : ℝ → ℝ := fun A =>
        Real.rpow (A - y₀) q - Real.rpow (A - y₁) q
      let N : ℝ → ℕ := fun L =>
        zeroCount (modelFunction k alpha amplification P L)
          (movingRectangle k alpha amplification y₀ y₁ delta L)
      let actionWidth : ℝ → ℝ := fun L =>
        (kappa L y₀ - kappa L y₁) / (2 * Real.pi)
      let densityScale : ℝ → ℝ := fun L => Real.rpow L (1 + q)
      let canonical : ℝ :=
        (Real.rpow ((5 / 2 - y₀) / alpha) q -
          Real.rpow ((5 / 2 - y₁) / alpha) q) / (2 * Real.pi)
      (0 < q ∧ q < 1) ∧
      (∀ A : ℝ, y₁ < A → deriv D A < 0) ∧
      0 < D (5 / 2) ∧
      0 < canonical ∧
      (∀ᶠ L : ℝ in atTop,
        y₁ < actionConstant amplification L ∧
          actionConstant amplification L ≤ 5 / 2 ∧
          D (actionConstant amplification L) ≥ D (5 / 2)) ∧
      (∀ᶠ L : ℝ in atTop, actionWidth L ≥ canonical) ∧
      0 < Filter.liminf
        (fun L : ℝ => actionWidth L) atTop ∧
      Filter.liminf
          (fun L : ℝ => (N L : ℝ) / densityScale L) atTop ≥
        Filter.liminf
          (fun L : ℝ => actionWidth L) atTop ∧
      Filter.liminf
          (fun L : ℝ => (N L : ℝ) / densityScale L) atTop ≥ canonical ∧
      (∀ᶠ L : ℝ in atTop,
        ∀ z : ℂ,
          z ∈ movingRectangle k alpha amplification y₀ y₁ delta L →
            modelFunction k alpha amplification P L z = 0 →
              z.im ≠ 0)

end

end MathlibPlus.Open.Analysis.FormalizationBatchO0268Claim15179
