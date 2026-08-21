import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.FormalizationBatch

noncomputable def gammaMeasure_claim10507 (α : ℝ) : Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun x => ENNReal.ofReal
      (Real.rpow x (α - 1) * Real.exp (-x) / Real.Gamma α))

noncomputable def gammaMoment_claim10507 (α : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ n ∂(gammaMeasure_claim10507 α)

/-- Andreief's integral representation for every generalized minor of the
moment matrix of the gamma measure. -/
def andreiefRepresentation_claim10507 : Prop :=
  ∀ (α : ℝ) (r : ℕ) (p q : Fin r → ℕ),
    0 < α →
      StrictMono p →
        StrictMono q →
          Matrix.det (fun i j => gammaMoment_claim10507 α (p i + q j)) =
            (1 / (Nat.factorial r : ℝ)) *
              ∫ x : (Fin r → ℝ),
                Matrix.det (fun i k => (x k) ^ (p i)) *
                  Matrix.det (fun j k => (x k) ^ (q j))
                ∂(MeasureTheory.Measure.pi
                  (fun _ : Fin r => gammaMeasure_claim10507 α))

end MathlibPlus.Open.FormalizationBatch
