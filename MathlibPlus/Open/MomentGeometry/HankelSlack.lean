import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.MomentGeometry

/--
Positive final Hankel slack and positivity at the preceding completed-Bezout rank do
not, in general, force positivity at the next rank: a negative value can remain at
 the final-Hankel boundary and persist after a positive displacement from it.

The completed Bezout matrix and the packet's factorial moment normalization are
expanded locally so this registry node has no dependency on a separately reviewed
definition.
-/
def hankelSlackDoesNotControlBezoutBoundary : Prop :=
  ∃ (N : ℕ) (m : ℕ → ℝ),
    2 ≤ N ∧
    let completedBezout :
        (rank : ℕ) → (ℕ → ℝ) → Matrix (Fin rank) (Fin rank) ℝ :=
      fun _ moments i j =>
        ∑ a ∈ Finset.range (min i.1 j.1 + 1),
          ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) *
            (moments a / (Nat.factorial (2 * a) : ℝ)) *
            (moments (i.1 + j.1 + 1 - a) /
              (Nat.factorial (2 * (i.1 + j.1 + 1 - a)) : ℝ))
    let boundaryMoments := Function.update m (2 * N - 1)
      (m (2 * N - 2) ^ 2 / m (2 * N - 3))
    0 < m 0 ∧
      0 < Matrix.det (completedBezout (N - 1) m) ∧
      0 < m (2 * N - 3) * m (2 * N - 1) - m (2 * N - 2) ^ 2 ∧
      Matrix.det (completedBezout N m) ≤ 0 ∧
      Matrix.det (completedBezout N boundaryMoments) < 0

end MathlibPlus.Open.MomentGeometry
