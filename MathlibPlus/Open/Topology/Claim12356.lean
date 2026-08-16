import Mathlib

namespace MathlibPlus.Open.Topology.Claim12356

/--
The open-ball specialization of the accumulating-counterexample interior
principle.  Acceptance of a certificate means membership in the displayed
metric ball, and sufficiency is required only on the target together with the
specified sequence.
-/
def metric_open_ball_specialization : Prop :=
  ∀ (X : Type*) (Y : Type*) [MetricSpace Y]
    (x₀ : X) (x : ℕ → X) (D : X → Y) (Good : X → Prop) (r : ℝ),
    0 < r →
    Filter.Tendsto (fun n : ℕ => D (x n)) Filter.atTop (nhds (D x₀)) →
    (∀ n : ℕ, 1 ≤ n → ¬ Good (x n)) →
    (∀ y : X,
      y ∈ ({x₀} : Set X) ∪ Set.range x →
      D y ∈ Metric.ball (D x₀) r → Good y) →
    ∃ n : ℕ,
      1 ≤ n ∧ ¬ Good (x n) ∧ D (x n) ∈ Metric.ball (D x₀) r

end MathlibPlus.Open.Topology.Claim12356
