import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open Filter
open scoped Topology

/-- A weakly-null unit tail witnesses a positive essential signal. -/
def claim3939 : Prop :=
  ∀ {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : E →L[ℝ] Y) (u : ℕ → E),
    (∀ j, ‖u j‖ = 1) →
      (∀ φ : E →L[ℝ] ℝ,
        Filter.Tendsto (fun j => φ (u j)) Filter.atTop (𝓝 0)) →
        let Λ := Filter.liminf (fun j => ‖T (u j)‖) Filter.atTop
        0 < Λ →
          ¬ IsCompactOperator (fun x => T x) ∧
            (∀ K : E →L[ℝ] Y,
              IsCompactOperator (fun x => K x) →
                Λ ≤ ‖T - K‖) ∧
            Λ ≤
              sInf
                {a : ℝ |
                  ∃ K : E →L[ℝ] Y,
                    IsCompactOperator (fun x => K x) ∧ a = ‖T - K‖}

end MathlibPlus.Open.ResearchFormalization
