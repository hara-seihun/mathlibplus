import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open

noncomputable def firstDifferingTranscriptCoordinate
    {d : ℕ} {A : Fin d → Type*}
    [∀ i, Fintype (A i)] {C : Type*}
    (code : C → ∀ i : Fin d, A i)
    (hcode : Function.Injective code) (x y : C) : ℕ := by
  classical
  exact if hxy : x = y then
    0
  else
    (Finset.min'
      (Finset.univ.filter (fun i : Fin d => code x i ≠ code y i))
      (by
        have hne : ∃ i : Fin d, code x i ≠ code y i := by
          by_contra h
          apply hxy
          apply hcode
          funext i
          by_contra hdiff
          exact h ⟨i, hdiff⟩
        exact (Finset.filter_nonempty_iff).2
          (by
            obtain ⟨i, hi⟩ := hne
            exact ⟨i, Finset.mem_univ i, hi⟩))).val

noncomputable def transcriptDistance
    {d : ℕ} {A : Fin d → Type*}
    [∀ i, Fintype (A i)] {C : Type*}
    (code : C → ∀ i : Fin d, A i)
    (hcode : Function.Injective code) (x y : C) : ℝ := by
  classical
  exact if x = y then
    0
  else
    ((2 : ℝ) ^
      firstDifferingTranscriptCoordinate code hcode x y)⁻¹

noncomputable def transcriptPrefixBound (d b : ℕ) (δ : ℝ) : ℝ :=
  Finset.sum (Finset.Icc (1 : ℕ) d) (fun m =>
    ((2 : ℝ) ^ (m - 1))⁻¹ *
      Real.sqrt
        (2 *
          ((m : ℝ) * Real.log (2 * (b : ℝ)) +
            Real.log (1 / δ))))

/-- The admitted finite transcript-prefix sub-Gaussian tail theorem. -/
noncomputable def finiteTranscriptPrefixSubGaussianTail : Prop :=
  ∀ (d b : ℕ),
    1 ≤ d →
    1 ≤ b →
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ],
      ∀ (A : Fin d → Type*) [∀ i, Fintype (A i)],
        (∀ i : Fin d, Fintype.card (A i) ≤ b) →
        ∀ (C : Type*) [Fintype C] [Nonempty C],
          ∀ (code : C → ∀ i : Fin d, A i),
            ∀ (hcode : Function.Injective code),
              ∀ (X : C → Ω → ℝ),
              (∀ x : C, Measurable (X x)) →
              (∀ (x y : C) (lam : ℝ),
                Integrable (fun ω => Real.exp (lam * (X x ω - X y ω))) μ ∧
                ∫ ω, Real.exp (lam * (X x ω - X y ω)) ∂μ ≤
                  Real.exp
                    (lam ^ 2 *
                      (transcriptDistance code hcode x y) ^ 2 /
                      2)) →
              ∀ (c₀ : C) (δ : ℝ),
                0 < δ →
                δ < 1 →
                μ {ω |
                    (Finset.univ.sup' Finset.univ_nonempty
                        (fun x : C => X x ω - X c₀ ω)) ≤
                      transcriptPrefixBound d b δ} ≥
                  ENNReal.ofReal (1 - δ) ∧
                transcriptPrefixBound d b δ ≤
                  4 * Real.sqrt (2 * Real.log (2 * (b : ℝ))) +
                    2 * Real.sqrt (2 * Real.log (1 / δ))

noncomputable def gammaThreeHalvesMoment (j : ℕ) (y : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ),
    (y + z) ^ (2 * j) *
      (Real.sqrt z * Real.exp (-z) / Real.Gamma (3 / 2 : ℝ))

noncomputable def gammaThreeHalvesEvaluationDeterminant (c : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 4 =>
    gammaThreeHalvesMoment j.1 (((i.1 + 1 : ℕ) : ℝ) * c))

def strictChebyshevSystemOnFirstLogarithmicCell : Prop :=
  ∀ (x : Fin 4 → ℝ),
    (∀ i j : Fin 4, i < j → x i < x j) →
    (∀ i : Fin 4, x i ∈ Set.Ioo (0 : ℝ) (Real.log 2)) →
    Matrix.det (fun i j : Fin 4 => gammaThreeHalvesMoment j.1 (x i)) ≠ 0

/-- The admitted Gamma(3/2,1) Appell determinant obstruction. -/
noncomputable def gammaEvenAppellShapeThreeHalvesRankFourFirstCellZero : Prop :=
  (∀ c : ℝ,
    0 < c →
    gammaThreeHalvesEvaluationDeterminant c =
      108 * c ^ 6 *
        (-35 + 150 * c + 1850 * c ^ 2 + 6400 * c ^ 3 +
          8629 * c ^ 4 + 5430 * c ^ 5 + 1400 * c ^ 6)) ∧
  gammaThreeHalvesEvaluationDeterminant (1 / 20 : ℝ) =
    -11890449 / 320000000000 ∧
  (-11890449 / 320000000000 : ℝ) < 0 ∧
  gammaThreeHalvesEvaluationDeterminant (1 / 10 : ℝ) =
    785511 / 1250000000 ∧
  (0 : ℝ) < 785511 / 1250000000 ∧
  (∃ cstar : ℝ,
    1 / 20 < cstar ∧
    cstar < 1 / 10 ∧
    Function.Injective (fun i : Fin 4 => (((i.1 + 1 : ℕ) : ℝ) * cstar)) ∧
    (∀ i j : Fin 4, i < j →
      (((i.1 + 1 : ℕ) : ℝ) * cstar) < (((j.1 + 1 : ℕ) : ℝ) * cstar)) ∧
    (∀ i : Fin 4,
      (((i.1 + 1 : ℕ) : ℝ) * cstar) ∈ Set.Ioo (0 : ℝ) (Real.log 2)) ∧
    gammaThreeHalvesEvaluationDeterminant cstar = 0 ∧
    ¬ strictChebyshevSystemOnFirstLogarithmicCell)

end MathlibPlus.Open
