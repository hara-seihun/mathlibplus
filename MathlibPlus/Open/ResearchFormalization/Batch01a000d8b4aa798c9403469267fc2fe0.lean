import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 4186: polarized Poisson–Charlier Parseval identity. -/
def polarizedPoissonCharlierParseval_4186
    (f g : ℂ → ℂ) (u v : ℕ → ℂ) : Prop :=
  ( (∀ z : ℂ,
        Complex.exp z * f z =
          tsum (fun n : ℕ => u n * z ^ n / (Nat.factorial n : ℂ))) ∧
    (∀ z : ℂ,
        Complex.exp z * g z =
          tsum (fun n : ℕ => v n * z ^ n / (Nat.factorial n : ℂ))) ) →
    ∀ x : ℂ,
      tsum (fun r : ℕ =>
        x ^ r * iteratedDeriv r f x * iteratedDeriv r g x /
          (Nat.factorial r : ℂ)) =
          Complex.exp (-x) *
            tsum (fun n : ℕ => u n * v n * x ^ n /
              (Nat.factorial n : ℂ))

end MathlibPlus.Open.ResearchFormalization
