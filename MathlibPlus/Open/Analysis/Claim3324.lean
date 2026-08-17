import Mathlib
import MathlibPlus.Open.Analysis.Claim3326

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.Analysis.Claim3324

noncomputable section

open MathlibPlus.Open.Analysis.Claim3326

private def validNode (N : ℝ → ℕ) (L : ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ n ≤ N L

private noncomputable def trainNode
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) : ℂ :=
  (y L n : ℂ) - Complex.I * (t L n : ℂ)

private noncomputable def shiftedBlaschke
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  Finset.prod (Finset.Icc 1 (n - 1)) (fun k =>
    (w - trainNode y t L k) /
      (w + star (trainNode y t L k)))

private def shiftedBlaschkeEnvelope
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ)
    (d : ℝ → ℝ) (theta : ℝ) : Prop :=
  ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
    ∃ Ctheta : ℝ, 0 ≤ Ctheta ∧
      ∀ᶠ L : ℝ in atTop,
        ∀ n : ℕ, validNode N L n → ∀ xi : ℝ,
          Real.log (‖shiftedBlaschke y t L n
              (-(theta * y L n : ℂ) + Complex.I * (xi : ℂ))‖ ^ 2) ≤
            (4 * Real.pi / d L + error L) *
                (theta * y L n) * L + Ctheta

/-- Claim 3324: the shifted Blaschke product has the uniform envelope with
an explicit little-o error and an explicit bounded theta-dependent term. -/
def shifted_blaschke_envelope_claim3324 : Prop :=
  ∀ (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ)
    (d eta q R : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (p r Y dLimit : ℝ),
    smoothMonotoneDenseTrain N y t d eta q R g p r Y dLimit →
    ∀ theta : ℝ, 0 < theta → theta < 1 →
      shiftedBlaschkeEnvelope N y t d theta

end
end MathlibPlus.Open.Analysis.Claim3324
