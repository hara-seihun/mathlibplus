import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.CompletedBezout

/--
Registry obligation for admitted claim 140.  The packet normalization is made
literal: `h j = m j / (2j)!`, and the rank-`N` completed Bezout matrix has
entry
`sum_{a=0}^{min(i,j)} (i+j+1-2a) h a h (i+j+1-a)`.
Only `m (2N-1)` varies in the derivative.
-/
def highestMomentDerivativeIdentity : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ m : ℕ → ℝ,
    let h : (ℕ → ℝ) → ℕ → ℝ :=
      fun moments j => moments j / (Nat.factorial (2 * j) : ℝ)
    let C : (rank : ℕ) → (ℕ → ℝ) → Matrix (Fin rank) (Fin rank) ℝ :=
      fun _ moments i j =>
        ∑ a ∈ Finset.range (min i.val j.val + 1),
          ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) *
            h moments a * h moments (i.val + j.val + 1 - a)
    let varyHighest : ℝ → ℕ → ℝ :=
      fun x j => if j = 2 * N - 1 then x else m j
    let determinantAlongHighest : ℝ → ℝ :=
      fun x => Matrix.det (C N (varyHighest x))
    HasDerivAt determinantAlongHighest
      (m 0 * Matrix.det (C (N - 1) m) /
        (2 * (Nat.factorial (4 * N - 3) : ℝ)))
      (m (2 * N - 1))

end MathlibPlus.Open.LinearAlgebra.CompletedBezout
