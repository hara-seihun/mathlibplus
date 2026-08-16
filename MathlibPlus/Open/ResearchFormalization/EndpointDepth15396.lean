import Mathlib

open Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.EndpointDepth15396

noncomputable section

/-- Claim 15396: a sublinear support radius alone does not force the
normalized first-moment depth to vanish, because a nearly cancelling finite
Fourier--Laplace denominator can amplify the quotient. -/
def endpointLocalityDoesNotControlEffectiveDepth_claim15396 : Prop :=
  let L : ℕ → ℝ := fun n => n + 1
  let r : ℕ → ℝ := fun _ => 1
  let τ : ℕ → Fin 2 → ℝ := fun _ j => if j = 0 then 0 else 1
  let a : ℕ → Fin 2 → ℂ := fun n j =>
    if j = 0 then 1 else -(1 - (1 / L n : ℂ))
  let B : ℕ → ℂ := fun n => ∑ j : Fin 2, a n j
  let m : ℕ → ℂ := fun n =>
    (∑ j : Fin 2, (τ n j : ℂ) * a n j) / B n
  Tendsto L atTop atTop ∧
    Tendsto (fun n => r n / L n) atTop (𝓝 0) ∧
    (∀ n : ℕ, ∀ j : Fin 2, |τ n j| ≤ r n) ∧
    ¬ Tendsto (fun n => ‖m n‖ / L n) atTop (𝓝 0)

end

end MathlibPlus.Open.ResearchFormalization.EndpointDepth15396
