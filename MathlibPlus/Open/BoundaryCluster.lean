import Mathlib

/-!
# Open boundary-cluster criteria

Faithful registry statement for the fixed-depth inverse-exponential consequence of vanishing
connected clusters.
-/

namespace MathlibPlus.Open.BoundaryCluster

open Filter Asymptotics

/-- If the connected coefficients in the formal identity
`Pₙ(X) = exp (∑_{j≥1} cₙⱼ Xʲ)` vanish relative to the corresponding powers of `aₙ`, then every
fixed coefficient has inverse-exponential asymptotics.  The second conclusion records the
source's equivalent reversed alternating extremal-coefficient form. -/
def vanishingClusterCriterion : Prop :=
  ∀ (a : ℕ → ℝ) (p c q : ℕ → ℕ → ℝ),
    (∀ n, 0 < a n) →
    Tendsto a atTop (nhds 0) →
    (∀ n, c n 0 = 0) →
    (∀ n, PowerSeries.mk (p n) =
      (PowerSeries.exp ℝ).subst (PowerSeries.mk (c n))) →
    (∀ n, c n 1 = a n) →
    (∀ j, 2 ≤ j → (fun n => c n j) =o[atTop] (fun n => a n ^ j)) →
    (∀ n k, k ≤ n → q n (n - k) = (-1 : ℝ) ^ k * p n k) →
    ∀ k,
      (fun n => p n k) ~[atTop] (fun n => a n ^ k / (k.factorial : ℝ)) ∧
      (fun n => q n (n - k)) ~[atTop]
        (fun n => (-a n) ^ k / (k.factorial : ℝ))

end MathlibPlus.Open.BoundaryCluster
