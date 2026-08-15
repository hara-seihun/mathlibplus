import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.FixedAnnulusWeakStarZero

open MeasureTheory Set Filter Topology

def intervalMellin3867 (a b : ℝ) (p : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Icc a b, Complex.exp ((s - 1) * Complex.log (x : ℂ)) * p x

def reflectionCommuting3867 (a b : ℝ) (p q : ℕ → ℝ → ℂ) : Prop :=
  ∀ j : ℕ, ∀ s : ℂ,
    intervalMellin3867 a b (p j) s * intervalMellin3867 a b (q j) (1 - s) =
      intervalMellin3867 a b (q j) s * intervalMellin3867 a b (p j) (1 - s)

def quotientsApproachZeta3867 (a b : ℝ) (p q : ℕ → ℝ → ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | 1 < s.re} →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ s ∈ K,
        ‖intervalMellin3867 a b (p j) s / intervalMellin3867 a b (q j) s -
            riemannZeta s‖ < ε

def normalized3867 (a b : ℝ) (p q : ℕ → ℝ → ℂ) : Prop :=
  ∀ j : ℕ,
    (∫ x in Icc a b, ‖p j x‖) + (∫ x in Icc a b, ‖q j x‖) = 1

def weakStarZero3867 (a b : ℝ) (p : ℕ → ℝ → ℂ) : Prop :=
  ∀ φ : ℝ → ℂ, ContinuousOn φ (Icc a b) →
    Tendsto (fun j : ℕ => ∫ x in Icc a b, φ x * p j x)
      atTop (𝓝 (0 : ℂ))

def fixedAnnulusWeakStarZeroCollapse3867 : Prop :=
  ∀ (a b : ℝ) (p q : ℕ → ℝ → ℂ),
    0 < a →
    a ≤ b →
    (∀ j : ℕ,
      MeasureTheory.IntegrableOn (p j) (Icc a b) ∧
        MeasureTheory.IntegrableOn (q j) (Icc a b)) →
    reflectionCommuting3867 a b p q →
    quotientsApproachZeta3867 a b p q →
    normalized3867 a b p q →
    weakStarZero3867 a b p ∧ weakStarZero3867 a b q

end MathlibPlus.Open.Analysis.FixedAnnulusWeakStarZero
