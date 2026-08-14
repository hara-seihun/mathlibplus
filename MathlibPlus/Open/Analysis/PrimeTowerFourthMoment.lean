import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def primeTowerTerm (p : ℕ) (t : ℝ) (k : ℕ) : ℂ :=
  ((Real.log (p : ℝ) / Real.rpow (p : ℝ) (((k + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
    Complex.exp (((-((k + 1 : ℕ) : ℝ) * t * Real.log (p : ℝ)) : ℂ) * Complex.I)

noncomputable def primeTowerSeries (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, primeTowerTerm p t k

noncomputable def primeTowerS (P : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, primeTowerSeries p t

noncomputable def primeTowerA (p : ℕ) : ℝ :=
  (Real.log (p : ℝ)) ^ 2 / ((p : ℝ) - 1)

noncomputable def primeTowerR2 (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, primeTowerA p

noncomputable def primeTowerR (P : Finset ℕ) : ℝ :=
  Real.sqrt (primeTowerR2 P)

noncomputable def primeTowerF (P : Finset ℕ) : ℝ :=
  (∑ p ∈ P, (Real.log (p : ℝ)) ^ 4 * ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3) +
    4 * (∑ p ∈ P, ∑ q ∈ P.filter (fun q => p < q), primeTowerA p * primeTowerA q)

noncomputable def primeTowerB (P : Finset ℕ) (α : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ ‖primeTowerS P t‖ ≥ α * primeTowerR P}

noncomputable def primeTowerDensity (P : Finset ℕ) (α T : ℝ) : ℝ :=
  (MeasureTheory.volume (primeTowerB P α ∩ Set.Icc 0 T)).toReal / T

noncomputable def ExactCesaroFourthMomentPrimeTower : Prop :=
  ∀ (P : Finset ℕ), P.Nonempty → (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, ∀ t : ℝ,
      Summable (fun k : ℕ => ‖primeTowerTerm p t k‖)) ∧
    Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖primeTowerS P t‖ ^ 4)
      Filter.atTop (nhds (primeTowerF P)) ∧
    (∀ α : ℝ, 0 ≤ α → α < 1 →
      Filter.liminf (fun T : ℝ => primeTowerDensity P α T) Filter.atTop ≥
          ((1 - α ^ 2) ^ 2 * (primeTowerR2 P) ^ 2 / primeTowerF P) ∧
        0 < ((1 - α ^ 2) ^ 2 * (primeTowerR2 P) ^ 2 / primeTowerF P))

end MathlibPlus.Open.Analysis
