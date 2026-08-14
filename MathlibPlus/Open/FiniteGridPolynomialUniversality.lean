import Mathlib

namespace MathlibPlus.Open

/-- The shifted quadratic grid from the admitted statement. -/
def finiteGridU (N : ℕ) : ℚ := (N : ℚ)^2 - 551 / 80000

/--
For every finite rational data set indexed by `0, ..., M`, there is a
rational polynomial of degree at most `M` interpolating the data at the
specified shifted quadratic grid.
-/
def finiteGridPolynomialUniversality : Prop :=
  ∀ M : ℕ, ∀ v : Fin (M + 1) → ℚ,
    ∃ p : Polynomial ℚ,
      p.degree ≤ (M : WithBot ℕ) ∧
        ∀ i : Fin (M + 1),
          Polynomial.eval (finiteGridU (690988 + i.1)) p = v i

end MathlibPlus.Open
