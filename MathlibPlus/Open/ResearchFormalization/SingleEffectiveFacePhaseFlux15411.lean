import Mathlib

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Classical

namespace MathlibPlus.Open.ResearchFormalization.SingleEffectiveFacePhaseFlux15411

noncomputable section

/-- The projective first-jet determinant for the shadow and effective face. -/
noncomputable def projectiveDelta (S B : ℕ → ℂ → ℂ) (L : ℕ) (z : ℂ) : ℂ :=
  S L z * deriv (B L) z - deriv (S L) z * B L z

/-- The phase flux on the regular part of a crossing graph. -/
noncomputable def phaseFlux
    (S B : ℕ → ℂ → ℂ) (Γ : ℕ → Set ℂ) (V : ℕ → Finset ℂ) : ℕ → ℝ :=
  fun L =>
    (1 / (2 * Real.pi)) *
      ∫ z in Γ L \ (V L : Set ℂ),
        ‖projectiveDelta S B L z / (S L z * B L z)‖
          ∂(Measure.hausdorffMeasure 1)

/-- A finite-set representative used to sum analytic zero orders. -/
noncomputable def finiteToFinset (s : Set ℂ) : Finset ℂ :=
  if h : s.Finite then h.toFinset else ∅

/-- The analytic-multiplicity zero count in a domain. -/
noncomputable def domainZeroCount
    (S B : ℕ → ℂ → ℂ) (D : ℕ → Set ℂ) : ℕ → ℕ :=
  fun L =>
    ∑ z ∈ (finiteToFinset
      {z : ℂ | z ∈ D L ∧ S L z + B L z = 0}),
      analyticOrderNatAt (fun w : ℂ => S L w + B L w) z

/-- The analytic-multiplicity count of positive-height zeros. -/
noncomputable def positiveHeightZeroCount
    (S B : ℕ → ℂ → ℂ) (D : ℕ → Set ℂ) : ℕ → ℕ :=
  fun L =>
    ∑ z ∈ (finiteToFinset
      {z : ℂ | z ∈ D L ∧ 0 < z.im ∧ S L z + B L z = 0}),
      analyticOrderNatAt (fun w : ℂ => S L w + B L w) z

/-- The boundary-endpoint and critical-jet charge. -/
noncomputable def criticalLoad
    (S B : ℕ → ℂ → ℂ) (D Γ : ℕ → Set ℂ)
    (V : ℕ → Finset ℂ) : ℕ → ℝ :=
  fun L =>
    ((finiteToFinset (Γ L ∩ frontier (D L))).card : ℝ) / 2 +
      ∑ v ∈ V L,
        ((analyticOrderNatAt (projectiveDelta S B L) v + 1 : ℕ) : ℝ)

/--
The one-effective-face phase-flux train.  The crossing graph is represented
by finitely many analytic regular edges and closed regular components; its
endpoint charge is therefore present even though the graph lies in the
closure of the positive-height domain.
-/
def claim15411_singleEffectiveFacePhaseFluxTrain : Prop :=
    ∀ (S B Φ₀ Φ₁ a₀ a₁ ε : ℕ → ℂ → ℂ)
      (D corridor Γ : ℕ → Set ℂ)
      (edgeCount loopCount : ℕ → ℕ)
      (edges : ∀ L, Fin (edgeCount L) → ℝ → ℂ)
      (loops : ∀ L, Fin (loopCount L) → ℝ → ℂ)
      (boundary : ℕ → ℝ → ℂ)
      (critical : ℕ → Finset ℂ)
      (δ ell : ℕ → ℝ),
      (∀ L : ℕ,
        IsOpen (D L) ∧
          Bornology.IsBounded (D L) ∧
          IsPreconnected (D L) ∧
          (D L).Nonempty ∧
          (∀ z ∈ D L, 0 < z.im) ∧
          AnalyticOnNhd ℂ (S L) (closure (D L)) ∧
          AnalyticOnNhd ℂ (B L) (closure (D L)) ∧
          (∀ z ∈ closure (D L),
            ¬ (S L z = 0 ∧ B L z = 0)) ∧
          AnalyticOnNhd ℝ (boundary L) Set.univ ∧
          Function.Periodic (boundary L) 1 ∧
          Set.range (boundary L) = frontier (D L) ∧
          (∀ s t : ℝ,
            s ∈ Set.Icc (0 : ℝ) 1 →
              t ∈ Set.Icc (0 : ℝ) 1 →
              boundary L s = boundary L t →
                s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
            deriv (boundary L) t ≠ 0) ∧
          Γ L =
            {z : ℂ | z ∈ closure (D L) ∧ ‖B L z‖ = ‖S L z‖} ∧
          (∀ z ∈ Γ L, S L z ≠ 0 ∧ B L z ≠ 0) ∧
          Set.Finite (Γ L ∩ frontier (D L)) ∧
          (∀ i : Fin (edgeCount L),
            AnalyticOnNhd ℝ (edges L i) Set.univ ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                deriv (edges L i) t ≠ 0)) ∧
          (∀ j : Fin (loopCount L),
            AnalyticOnNhd ℝ (loops L j) Set.univ ∧
              loops L j 0 = loops L j 1 ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                deriv (loops L j) t ≠ 0)) ∧
          Γ L =
            (⋃ i : Fin (edgeCount L),
              edges L i '' Set.Icc (0 : ℝ) 1) ∪
              (⋃ j : Fin (loopCount L),
                loops L j '' Set.Icc (0 : ℝ) 1) ∧
          (∀ z, z ∈ Γ L → z ∈ frontier (D L) →
            (∃ i : Fin (edgeCount L), ∃ t u : ℝ,
              t ∈ Set.Icc (0 : ℝ) 1 ∧
                u ∈ Set.Icc (0 : ℝ) 1 ∧
                edges L i t = z ∧
                boundary L u = z ∧
                Complex.im (conj (deriv (edges L i) t) *
                  deriv (boundary L) u) ≠ 0) ∨
            (∃ j : Fin (loopCount L), ∃ t u : ℝ,
              t ∈ Set.Icc (0 : ℝ) 1 ∧
                u ∈ Set.Icc (0 : ℝ) 1 ∧
                loops L j t = z ∧
                boundary L u = z ∧
                Complex.im (conj (deriv (loops L j) t) *
                  deriv (boundary L) u) ≠ 0)) ∧
          (∀ z, z ∈ (critical L : Set ℂ) ↔
            z ∈ Γ L ∧ projectiveDelta S B L z = 0) ∧
          Set.Finite (critical L : Set ℂ) ∧
          0 ≤ ell L ∧
          ENNReal.ofReal (ell L) ≤
            Measure.hausdorffMeasure 1
              (Γ L \ (critical L : Set ℂ))) ∧
      (∀ L : ℕ,
        IsOpen (corridor L) ∧
          closure (D L) ⊆ corridor L ∧
          Γ L ⊆ corridor L ∧
          AnalyticOnNhd ℂ (Φ₀ L) (corridor L) ∧
          AnalyticOnNhd ℂ (Φ₁ L) (corridor L) ∧
          AnalyticOnNhd ℂ (a₀ L) (corridor L) ∧
          AnalyticOnNhd ℂ (a₁ L) (corridor L) ∧
          AnalyticOnNhd ℂ (ε L) (corridor L) ∧
          (∀ z ∈ corridor L,
            S L z = Complex.exp (-(L : ℂ) * Φ₀ L z) * a₀ L z) ∧
          (∀ z ∈ corridor L,
            B L z = Complex.exp (-(L : ℂ) * Φ₁ L z) * a₁ L z *
              (1 + ε L z)) ∧
          (∀ z ∈ Γ L,
            a₀ L z ≠ 0 ∧ a₁ L z ≠ 0 ∧ 1 + ε L z ≠ 0)) →
      (∀ L : ℕ,
        δ L = sInf (Set.image
          (fun z : ℂ => ‖deriv (Φ₁ L) z - deriv (Φ₀ L) z‖)
          (Γ L))) →
      (∀ η : ℝ, 0 < η →
        ∀ᶠ L : ℕ in Filter.atTop,
          ∀ z ∈ Γ L, ‖ε L z‖ ≤ η) →
      (∀ η : ℝ, 0 < η →
        ∀ᶠ L : ℕ in Filter.atTop,
          ∀ z ∈ Γ L,
            ‖deriv (a₁ L) z / a₁ L z -
                deriv (a₀ L) z / a₀ L z +
                deriv (ε L) z / (1 + ε L z)‖ ≤
              η * (L : ℝ) * δ L) →
      (∀ η : ℝ, 0 < η →
        ∀ᶠ L : ℕ in Filter.atTop,
          ∀ z ∈ Γ L \ (critical L : Set ℂ),
            ‖projectiveDelta S B L z /
                (S L z * B L z)‖ ≥
              (1 - η) * (L : ℝ) * δ L) ∧
      (∀ η : ℝ, 0 < η →
        ∀ᶠ L : ℕ in Filter.atTop,
          phaseFlux S B Γ critical L ≥
            (1 - η) * (L : ℝ) * δ L * ell L /
              (2 * Real.pi)) ∧
      (∀ η : ℝ, 0 < η →
        ∀ᶠ L : ℕ in Filter.atTop,
          (domainZeroCount S B D L : ℝ) ≥
            (1 - η) * (L : ℝ) * δ L * ell L /
              (2 * Real.pi) -
                criticalLoad S B D Γ critical L) ∧
      ((∀ η : ℝ, 0 < η →
          ∀ᶠ L : ℕ in Filter.atTop,
            |criticalLoad S B D Γ critical L| ≤
              η * (L : ℝ) * δ L * ell L) →
        ∃ c : ℝ, 0 < c ∧
          ∀ᶠ L : ℕ in Filter.atTop,
            (positiveHeightZeroCount S B D L : ℝ) ≥
              c * (L : ℝ) * δ L * ell L)

end

end MathlibPlus.Open.ResearchFormalization.SingleEffectiveFacePhaseFlux15411
