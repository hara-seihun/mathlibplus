import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim2478_exactEndpointKernelRealization : Prop := by
  classical
  exact ∀ (A : ℝ) (k : ℝ → ℝ) (c : ℝ),
    0 < A → ContDiff ℝ ⊤ k → Function.support k ⊆ Set.Ico 0 A →
    c > Real.exp A →
    ∃ p : ℝ → ℝ,
      ContDiff ℝ ⊤ p ∧ (∀ v, p (-v) = p v) ∧ p 0 = 0 ∧
        (∫ v : ℝ, p v) = 0 ∧
        Function.support p ⊆ {v | |v| < Real.exp A / c} ∧
        (∀ x : ℝ,
          (Real.exp (x / 2) / Real.sqrt c *
              ∑ n ∈ Finset.Icc 1 (Nat.ceil (c * Real.exp (-x))),
                if (1 : ℝ) ≤ n ∧ (n : ℝ) < c * Real.exp (-x) then
                  p ((n : ℝ) * Real.exp x / c)
                else 0) = k x)

def claim2481_closedStripTransformBound : Prop := by
  exact ∀ (A Y c δ : ℝ) (k : ℝ → ℝ) (z : ℂ),
    0 ≤ A → 0 ≤ Y → 0 < c → |z.im| ≤ Y →
    let G : ℂ → ℂ := fun w =>
      (δ : ℂ) * ∫ x in (0 : ℝ)..A,
        (k x : ℂ) * Complex.cos (w * ((x - Real.log c / 2 : ℝ) : ℂ))
    ‖G z‖ ≤ |δ| * c ^ (Y / 2) * Real.exp (A * Y) *
      ∫ x in (0 : ℝ)..A, |k x|

def claim2482_cQuarterCorrectionsVanishLocallyUniformly : Prop := by
  classical
  exact ∀ (A : ℝ) (k : ℝ → ℝ) (c δ : ℕ → ℝ) (K : ℝ),
    0 ≤ A → 0 ≤ K →
    (∀ n, 0 < c n) →
    Tendsto c atTop atTop →
    (∀ n, |δ n| ≤ K * Real.rpow (c n) (-1 / 4 : ℝ)) →
    let G : ℝ → ℝ → ℂ → ℂ := fun cn dn w =>
      (dn : ℂ) * ∫ x in (0 : ℝ)..A,
        (k x : ℂ) * Complex.cos (w * ((x - Real.log cn / 2 : ℝ) : ℂ))
    (∀ C : Set ℂ, IsCompact C → C ⊆ {z | |z.im| < 1 / 2} →
      ∀ ε, 0 < ε →
        ∀ᶠ n in atTop, ∀ z ∈ C, ‖G (c n) (δ n) z‖ < ε) ∧
      (∀ Y, 0 ≤ Y → Y < 1 / 2 → ∀ ε, 0 < ε →
        ∀ᶠ n in atTop, ∀ z, |z.im| ≤ Y → ‖G (c n) (δ n) z‖ < ε)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
