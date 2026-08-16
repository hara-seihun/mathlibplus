import Mathlib

open Filter
open scoped ENNReal lp Topology

namespace MathlibPlus.Open.ResearchFormalization.O0329AdaptiveObservers

/-- Claim 15504: the standard coordinate projections give compact finite-rank
observers converging strongly and weakly to zero while tracking a weakly-null
unit source. -/
def claim15504 : Prop :=
  let H := lp (fun _ : ℕ => ℝ) 2
  let e : ℕ → H := fun j => lp.single 2 j 1
  let P : ℕ → H →L[ℝ] H :=
    fun j => (innerSL ℝ (e j)).smulRight (e j)
  (∀ x : H, Tendsto (fun j => P j x) atTop (𝓝 0)) ∧
    (∀ x y : H,
      Tendsto (fun j => inner ℝ (P j x) y) atTop (𝓝 0)) ∧
    (∀ x : H, Tendsto (fun j => ‖P j x‖) atTop (𝓝 0)) ∧
    (∀ j : ℕ,
      IsCompact (closure (P j '' Metric.closedBall (0 : H) 1))) ∧
    (∀ j : ℕ,
      Module.finrank ℝ (LinearMap.range ((P j).toLinearMap)) = 1) ∧
    (∀ j : ℕ, ‖e j‖ = 1) ∧
    (∀ x : H,
      Tendsto (fun j => inner ℝ x (e j)) atTop (𝓝 0)) ∧
    (∀ j : ℕ, P j (e j) = e j ∧ ‖P j (e j)‖ = 1) ∧
    ¬ (∀ u : ℕ → H,
      (∀ j, ‖u j‖ = 1) →
      (∀ x : H,
        Tendsto (fun j => inner ℝ x (u j)) atTop (𝓝 0)) →
      Tendsto (fun j => ‖P j (u j)‖) atTop (𝓝 0))

/-- Claim 15505: exact tracking of the standard weakly-null unit basis needs
no rank growth; every coordinate observer has rank one. -/
def claim15505 : Prop :=
  let H := lp (fun _ : ℕ => ℝ) 2
  let e : ℕ → H := fun j => lp.single 2 j 1
  let P : ℕ → H →L[ℝ] H :=
    fun j => (innerSL ℝ (e j)).smulRight (e j)
  (∀ j : ℕ, ‖e j‖ = 1) ∧
    (∀ x : H,
      Tendsto (fun j => inner ℝ x (e j)) atTop (𝓝 0)) ∧
    (∀ j : ℕ, P j (e j) = e j ∧ ‖P j (e j)‖ = 1) ∧
    (∀ j : ℕ,
      Module.finrank ℝ (LinearMap.range ((P j).toLinearMap)) = 1)

end MathlibPlus.Open.ResearchFormalization.O0329AdaptiveObservers
