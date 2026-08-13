import Mathlib

namespace MathlibPlus.Analysis.Claim42849

/-!
The constants are supplied as a sequence `C : ℕ → ℝ`; the definition keeps
both the nonnegativity of every `C_N` and the uniform-in-`t` bound explicit.
The complex absolute values are represented by the norm on `ℂ`.
-/

/-- Joint rapid decrease of two complex-valued real channels with explicit
polynomial-weight bounds. -/
def jointlyRapidlyDecreasing
    (H J : ℝ → ℂ) (C : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 0 ≤ C N ∧
    ∀ t : ℝ,
      (1 + |t|) ^ N * (‖H t‖ + ‖J t‖) ≤ C N

end MathlibPlus.Analysis.Claim42849
