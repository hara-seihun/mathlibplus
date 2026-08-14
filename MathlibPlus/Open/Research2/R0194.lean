import Mathlib

namespace MathlibPlus.Open.Research2.R0194

def solid_companion_minors
    (A : ℕ → ℕ → ℝ) (D : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ p q k : ℕ,
    D p q k =
      Matrix.det (fun i j : Fin k =>
        A (p + (i : ℕ)) (q + (j : ℕ)))

def grouped_sylvester_packet
    (D S : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ p q k : ℕ, 2 ≤ k →
    S p q k =
      D p q (k - 1) * D (p + 1) (q + 1) (k - 1) -
        D (p + 1) q (k - 1) * D p (q + 1) (k - 1)

end MathlibPlus.Open.Research2.R0194
