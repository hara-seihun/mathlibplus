import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchO0078

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0080

noncomputable def squarePortIntegral (σ t : ℝ) (P : ℝ → ℝ) : ℂ :=
  ∫ u : ℝ in Set.Ioi (0 : ℝ),
    (P u : ℂ) *
      Complex.exp (-(σ : ℂ) * (u : ℂ) +
        Complex.I * (t : ℂ) * (u : ℂ)) *
      (MathlibPlus.Open.ResearchFormalization.BatchO0078.h6 u : ℂ)

noncomputable def squarePort0 (σ t : ℝ) : ℂ :=
  squarePortIntegral σ t (fun u => u ^ 2)

noncomputable def squarePort1 (σ t r : ℝ) : ℂ :=
  squarePortIntegral σ t (fun u => u * (2 * r - u))

noncomputable def squarePort2 (σ t r : ℝ) : ℂ :=
  squarePortIntegral σ t (fun u => (u - 2 * r) ^ 2)

def additivePortTarget (S₀ S₁ S₂ : ℂ) : Prop :=
  0 ≤ ‖S₀‖ ^ 2 + ‖S₂‖ ^ 2 - 2 * ‖S₁‖ ^ 2

def multiplicativeCauchySchwarz (S₀ S₁ S₂ : ℂ) : Prop :=
  ‖S₁‖ ^ 2 ≤ ‖S₀‖ * ‖S₂‖

def portPhaseCondition (S₀ S₁ S₂ : ℂ) : Prop :=
  ((S₀ = 0 ∨ S₂ = 0) → S₁ = 0) ∧
    ((S₀ ≠ 0 ∧ S₂ ≠ 0) →
      let ratio : ℂ := S₁ ^ 2 / (S₀ * S₂)
      ratio.im = 0 ∧ 0 ≤ ratio.re)

def positiveHermitianGram (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ i j, A i j = starRingEnd ℂ (A j i)) ∧
    (∀ w : Fin 2 → ℂ,
      0 ≤
        (∑ i : Fin 2, ∑ j : Fin 2,
          starRingEnd ℂ (w i) * A i j * w j).re)

noncomputable def diagonalUnitaryCongruence
    (u v S₀ S₁ S₂ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![starRingEnd ℂ u * S₀ * u, starRingEnd ℂ u * S₁ * v;
     starRingEnd ℂ v * S₁ * u, starRingEnd ℂ v * S₂ * v]

def diagonalUnitaryPositiveGram (S₀ S₁ S₂ : ℂ) : Prop :=
  ∃ u v : ℂ,
    ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      positiveHermitianGram (diagonalUnitaryCongruence u v S₀ S₁ S₂)

/-- The complete admitted comparison between the additive Lorentz target and
multiplicative Cauchy--Schwarz, retaining the phase and diagonal-unitary
conditions for the actual square-port carrier. -/
def claim12180 : Prop :=
  (∀ x y z : ℝ,
    x ^ 2 + y ^ 2 - 2 * z ^ 2 =
      (x - y) ^ 2 + 2 * (x * y - z ^ 2)) ∧
  (∀ S₀ S₁ S₂ : ℂ,
    multiplicativeCauchySchwarz S₀ S₁ S₂ →
      additivePortTarget S₀ S₁ S₂) ∧
  (∀ S₀ S₁ S₂ : ℂ,
    diagonalUnitaryPositiveGram S₀ S₁ S₂ →
      multiplicativeCauchySchwarz S₀ S₁ S₂) ∧
  (¬ ∀ S₀ S₁ S₂ : ℂ,
    additivePortTarget S₀ S₁ S₂ →
      multiplicativeCauchySchwarz S₀ S₁ S₂) ∧
  (¬ ∀ S₀ S₁ S₂ : ℂ,
    multiplicativeCauchySchwarz S₀ S₁ S₂ →
      portPhaseCondition S₀ S₁ S₂) ∧
  (let σ : ℝ := 99 / 100
   let t : ℝ := 11153 / 100
   let r : ℝ := -
     MathlibPlus.Open.ResearchFormalization.BatchO0078.q6 σ t
   let S₀ : ℂ := squarePort0 σ t
   let S₁ : ℂ := squarePort1 σ t r
   let S₂ : ℂ := squarePort2 σ t r
   additivePortTarget S₀ S₁ S₂ ∧
     ¬ multiplicativeCauchySchwarz S₀ S₁ S₂)

end MathlibPlus.Open.ResearchFormalization.BatchO0080
