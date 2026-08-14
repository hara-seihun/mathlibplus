import Mathlib

namespace MathlibPlus.Open.NewResearch2.Analysis

/--
The endpoint-local phase-volume implication from the leased claim.  The carrier is
an explicit finite union of regular parametrized complex arcs; `gamma` is their
union, `length` is their total arclength, and the two counts are literal counts
of zeros of `X + D` in that carrier.
-/
def endpointLocalLowCancellationPhaseVolumeTrain
    (X D : ℕ → ℂ → ℂ)
    (J : ℕ → ℕ)
    (arcs : ∀ L, Fin (J L) → ℝ → ℂ)
    (theta : ∀ L, Fin (J L) → ℝ)
    (r S : ℕ → ℕ)
    (C T : ℕ → ℕ → ℝ)
    (ell : ℕ → ℝ) : Prop := by
  classical
  let gamma : ℕ → Set ℂ := fun L =>
    ⋃ j : Fin (J L), arcs L j '' Set.Icc (0 : ℝ) 1
  let length : ℕ → ℝ := fun L =>
    ∑ j : Fin (J L), ∫ t in Set.Icc (0 : ℝ) 1, ‖deriv (arcs L j) t‖
  let zeroCount : ℕ → ℕ := fun L =>
    Set.ncard {z : ℂ | z ∈ gamma L ∧ X L z + D L z = 0}
  let positiveZeroCount : ℕ → ℕ := fun L =>
    Set.ncard
      {z : ℂ | z ∈ gamma L ∧ 0 < z.im ∧ X L z + D L z = 0}
  exact
    (∀ L (j : Fin (J L)),
        ContDiff ℝ 1 (arcs L j) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
            ‖deriv (arcs L j) t‖ ≠ 0 ∧ 0 < (arcs L j t).im) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
            (Complex.log (-X L (arcs L j t) / D L (arcs L j t))).im =
              theta L j)) ∧
    (∀ L z, z ∈ gamma L → X L z ≠ 0 ∧ D L z ≠ 0) ∧
    (∀ L, ell L = length L) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (L : ℕ) in Filter.atTop, |(r L : ℝ)| < ε * (L : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (L : ℕ) in Filter.atTop, ∀ z ∈ gamma L,
        ‖deriv (X L) z / X L z‖ / (L : ℝ) +
            ((r L : ℝ) / (L : ℝ)) * C L (r L) + T L (r L) < ε) →
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (L : ℕ) in Filter.atTop, ∀ z ∈ gamma L,
        |‖deriv (fun w : ℂ => Complex.log (-X L w / D L w)) z‖ /
              (L : ℝ) - 1| < ε) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (L : ℕ) in Filter.atTop,
        (zeroCount L : ℝ) ≥
          (1 - ε) * (L : ℝ) * ell L / (2 * Real.pi) - (J L : ℝ)) ∧
    (((∃ a b : ℝ,
          0 < a ∧ 0 < b ∧
            (∀ᶠ (L : ℕ) in Filter.atTop,
              0 < S L ∧ a * (S L : ℝ) ≤ ell L ∧
                ell L ≤ b * (S L : ℝ))) ∧
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ (L : ℕ) in Filter.atTop,
            |(J L : ℝ)| ≤ ε * (L : ℝ) * (S L : ℝ))) →
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ (L : ℕ) in Filter.atTop,
          c * (L : ℝ) * (S L : ℝ) ≤ (positiveZeroCount L : ℝ))

end MathlibPlus.Open.NewResearch2.Analysis
