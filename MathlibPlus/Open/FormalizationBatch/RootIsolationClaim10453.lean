import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- The polynomial `S` supplied by the exact reciprocal-reduction repair context. -/
noncomputable def S_claim10453 : Polynomial ℝ :=
  Polynomial.C (403104 : ℝ) * Polynomial.X ^ 9 +
    Polynomial.C (403104 : ℝ) * Polynomial.X ^ 8 -
    Polynomial.C (1612416 : ℝ) * Polynomial.X ^ 7 -
    Polynomial.C (1612416 : ℝ) * Polynomial.X ^ 6 +
    Polynomial.C (1894672 : ℝ) * Polynomial.X ^ 5 +
    Polynomial.C (1854528 : ℝ) * Polynomial.X ^ 4 -
    Polynomial.C (654836 : ℝ) * Polynomial.X ^ 3 -
    Polynomial.C (604656 : ℝ) * Polynomial.X ^ 2 +
    Polynomial.C (36581 : ℝ) * Polynomial.X +
    Polynomial.C (26931 : ℝ)

def signChangeIsolatedRoot_claim10453 (p : Polynomial ℝ) (r : ℝ) : Prop :=
  p.eval r = 0 ∧
    ∃ ε : ℝ, 0 < ε ∧
      ((∀ x : ℝ, r - ε < x → x < r → 0 < p.eval x) ∧
          (∀ x : ℝ, r < x → x < r + ε → p.eval x < 0) ∨
        (∀ x : ℝ, r - ε < x → x < r → p.eval x < 0) ∧
          (∀ x : ℝ, r < x → x < r + ε → 0 < p.eval x))

/-- `S` has exactly nine sign-change-isolated real roots, eight strictly between
`-√2` and `√2`, and one above `√2`. -/
def rootIsolationCertificate_claim10453 : Prop :=
  ∃ roots : Fin 9 → ℝ,
    Function.Injective roots ∧
      (∀ i, signChangeIsolatedRoot_claim10453 S_claim10453 (roots i)) ∧
      (∀ x : ℝ, S_claim10453.eval x = 0 → ∃ i, x = roots i) ∧
      ∃ j : Fin 9,
        Real.sqrt 2 < roots j ∧
          ∀ i, i ≠ j → -Real.sqrt 2 < roots i ∧ roots i < Real.sqrt 2

end MathlibPlus.Open.FormalizationBatch
