import Mathlib
import MathlibPlus.Analysis.ReciprocalXi

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0268Claim15178

noncomputable section

def admissibleProfile
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

def xiPlane (z : ℂ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + Complex.I * z)

def profileValue
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  (P L).eval
    (z ^ 2 / (Real.rpow L (1 / (k : ℝ)) : ℂ))

def profileCarrier
    (P : ℝ → Polynomial ℂ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  xiPlane z / (2 * (Real.pi : ℂ)) * profileValue P k L z

def diniCarrier (L : ℝ) (z : ℂ) : ℂ :=
  (z * Complex.sin ((L : ℂ) * z) -
      (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 + (1 / 4 : ℂ))

def modelFunction
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  profileCarrier P k L z * Complex.exp (-(alpha : ℂ) * z ^ (2 * k)) -
    (amplification L * Real.exp (-5 * L / 2) : ℂ) * diniCarrier L z

def actionConstant
    (amplification : ℝ → ℝ) (L : ℝ) : ℝ :=
  (5 : ℝ) / 2 - Real.log (amplification L) / L

def transitionScale (k : ℕ) (L : ℝ) : ℝ :=
  Real.rpow L (1 / (2 * (k : ℝ)))

def movingKappa
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (L y : ℝ) : ℝ :=
  Real.rpow
    ((actionConstant amplification L - y) / alpha)
    (1 / (2 * (k : ℝ)))

def movingRectangle
    (k : ℕ) (alpha : ℝ) (amplification : ℝ → ℝ)
    (y₀ y₁ L : ℝ) : Set ℂ :=
  {z : ℂ |
    movingKappa k alpha amplification L y₁ * transitionScale k L ≤ z.re ∧
      z.re ≤ movingKappa k alpha amplification L y₀ * transitionScale k L ∧
      y₀ ≤ z.im ∧ z.im ≤ y₁}

def zeroMultiplicity
    (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  if f z = 0 then (meromorphicOrderAt f z).untop₀.toNat else 0

def countedZeroSet (f : ℂ → ℂ) (region : Set ℂ) : Set (ℂ × ℕ) :=
  {p | p.1 ∈ region ∧ p.2 < zeroMultiplicity f p.1}

def zeroCount (f : ℂ → ℂ) (region : Set ℂ) : ℕ :=
  (countedZeroSet f region).ncard

/-- Claim 15178: the actual Xi-shadow/negative-Dini model has the stated
macroscopic moving-rectangle multiplicity density and eventual nonreal zeros. -/
def claim15178 : Prop :=
  ∀ (k : ℕ) (alpha : ℝ)
    (amplification : ℝ → ℝ)
    (P : ℝ → Polynomial ℂ) (d : ℝ → ℕ)
    (B : ℝ → ℝ) (coeff : ℝ → ℕ → ℂ)
    (y₀ y₁ : ℝ),
    admissibleProfile k P d B coeff →
      0 < alpha →
      (∀ L : ℝ, 1 ≤ amplification L) →
      Tendsto (fun L : ℝ => amplification L * Real.exp (-2 * L))
        atTop (𝓝 0) →
      0 < y₀ → y₀ < y₁ → y₁ < (1 : ℝ) / 2 →
      let q : ℝ := 1 / (2 * (k : ℝ))
      let kappa : ℝ → ℝ → ℝ := fun L y =>
        Real.rpow ((actionConstant amplification L - y) / alpha) q
      let densityScale : ℝ → ℝ := fun L => Real.rpow L (1 + q)
      let N : ℝ → ℕ := fun L =>
        zeroCount (modelFunction k alpha amplification P L)
          (movingRectangle k alpha amplification y₀ y₁ L)
      let density : ℝ → ℝ := fun L =>
        (kappa L y₀ - kappa L y₁) / (2 * Real.pi)
      (Filter.liminf
          (fun L : ℝ => (N L : ℝ) / densityScale L) atTop ≥
        Filter.liminf (fun L : ℝ => density L) atTop) ∧
      0 < Filter.liminf (fun L : ℝ => density L) atTop ∧
      (∀ᶠ L : ℝ in atTop,
        ∀ z : ℂ,
          z ∈ movingRectangle k alpha amplification y₀ y₁ L →
            modelFunction k alpha amplification P L z = 0 →
              z.im ≠ 0)

end

end MathlibPlus.Open.ResearchFormalization.O0268Claim15178
