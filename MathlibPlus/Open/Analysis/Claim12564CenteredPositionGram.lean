import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The real `L²` inner product written on representatives. -/
noncomputable def realL2Inner_12564 (f g : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, f u * g u

/-- Translation/centered-position Gram identities for an even real source. -/
def centeredPositionGramIdentities_12564 : Prop :=
  ∀ (w : ℝ → ℝ),
    Even w →
    MeasureTheory.MemLp w 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
    MeasureTheory.MemLp (fun u : ℝ => u * w u) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
    let A : ℝ → ℝ := fun D =>
      ∫ v : ℝ, w (v - D) * w (v + D)
    let J : ℝ → ℝ := fun D =>
      ∫ v : ℝ, v ^ 2 * w (v - D) * w (v + D)
    ∀ (x x' : ℝ),
      let D : ℝ := x - x'
      let f_x : ℝ → ℝ := fun u => w (u - 2 * x)
      let f_x' : ℝ → ℝ := fun u => w (u - 2 * x')
      let p_x : ℝ → ℝ := fun u => (u - 2 * x) * f_x u
      let p_x' : ℝ → ℝ := fun u => (u - 2 * x') * f_x' u
      realL2Inner_12564 f_x f_x' = A D ∧
        realL2Inner_12564 f_x p_x' = D * A D ∧
          realL2Inner_12564 p_x f_x' = -D * A D ∧
            realL2Inner_12564 p_x p_x' = J D - D ^ 2 * A D

end MathlibPlus.Open.Analysis
