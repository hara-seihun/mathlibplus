import Mathlib

open Filter

namespace MathlibPlus.Open.ResearchFormalization

def claim3946_output_escape_adjoint_packing : Prop :=
  ∀ {𝕜 E Y : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (u : ℕ → E) (T : ℕ → E →L[𝕜] Y),
    (∀ j, ‖u j‖ ≤ 1) →
    (∀ x : E, Tendsto (fun j => inner 𝕜 (u j) x) atTop (nhds 0)) →
    0 < Filter.liminf (fun j => ‖T j (u j)‖) atTop →
    (¬ IsCompact (closure (Set.range (fun j => T j (u j)))) ∨
      ∃ z : Y, ‖z‖ = 1 ∧
        ∃ s : ℕ → ℕ, StrictMono s ∧
          ∀ r : ℝ, 0 < r →
            r < Filter.liminf (fun j => ‖T j (u j)‖) atTop →
            ∃ t : ℕ → ℕ, StrictMono t ∧
              ∀ a b : ℕ, a ≠ b →
                r < ‖(ContinuousLinearMap.adjoint (T (s (t a))) z) -
                  (ContinuousLinearMap.adjoint (T (s (t b))) z)‖)

end MathlibPlus.Open.ResearchFormalization
