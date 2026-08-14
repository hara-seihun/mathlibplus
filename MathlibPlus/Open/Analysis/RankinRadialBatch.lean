import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable def radialDensity (α u : ℝ) : ℝ :=
  if 0 < u then Real.rpow u (α - 1) * Real.exp (-u) / Real.Gamma α else 0

noncomputable def radialMeasure (α : ℝ) : Measure ℝ :=
  (Measure.restrict volume (Set.Ioi (0 : ℝ))).withDensity
    (fun u => ENNReal.ofReal (radialDensity α u))

noncomputable def radialGenerator (α : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => u * deriv f u + ((α - u) / 2) * f u

noncomputable def shiftedRadialGenerator (α μ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => radialGenerator α f u + μ * f u

noncomputable def radialJet (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => (1 : ℝ)
  | j + 1 => radialGenerator α (radialJet α j)

noncomputable def shiftedRadialJet (α μ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => (1 : ℝ)
  | j + 1 => shiftedRadialGenerator α μ (shiftedRadialJet α μ j)

noncomputable def radialInner (α : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ u, f u * g u ∂(radialMeasure α)

noncomputable def radialGram (α : ℝ) (m : ℕ) (jets : ℕ → ℝ → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => radialInner α (jets (i : ℕ)) (jets (j : ℕ))

noncomputable def radialHankel (α : ℝ) (m : ℕ) (jets : ℕ → ℝ → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => radialInner α (fun _ => (1 : ℝ)) (jets ((i : ℕ) + (j : ℕ)))

def risingFactorial (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => risingFactorial α j * (α + j)

noncomputable def monicLaguerreNorm (α : ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * risingFactorial α j

noncomputable def laguerreLeadingCoefficient (j : ℕ) : ℝ :=
  (-((1 : ℝ) / 2)) ^ j

def centeredRankinRadialGeneratorClaim : Prop :=
  ∀ (α s μ : ℝ), 0 < α → μ = (1 - s) / 2 →
    radialMeasure α Set.univ = 1 ∧
      (∀ (j : ℕ) (u : ℝ),
        shiftedRadialJet α μ j u =
          Finset.sum (Finset.range (j + 1)) (fun r =>
            (Nat.choose j r : ℝ) * μ ^ (j - r) * radialJet α r u)) ∧
      (∀ (m : ℕ),
        Matrix.det (radialGram α m (shiftedRadialJet α μ)) =
            Matrix.det (radialGram α m (radialJet α)) ∧
          Matrix.det (radialHankel α m (shiftedRadialJet α μ)) =
            Matrix.det (radialHankel α m (radialJet α)))

def balancedGramDeterminantClaim : Prop :=
  ∀ (α : ℝ) (m : ℕ), 0 < α →
    Matrix.det (radialGram α m (radialJet α)) =
        Finset.prod (Finset.range (m + 1)) (fun j =>
          monicLaguerreNorm α j * (laguerreLeadingCoefficient j) ^ 2) ∧
      Matrix.det (radialGram α m (radialJet α)) =
        ((2 : ℝ) ^ (m * (m + 1)))⁻¹ *
          Finset.prod (Finset.range (m + 1)) (fun j =>
            (j.factorial : ℝ) * risingFactorial α j) ∧
      0 < Matrix.det (radialGram α m (radialJet α))

end MathlibPlus.Open.Analysis
