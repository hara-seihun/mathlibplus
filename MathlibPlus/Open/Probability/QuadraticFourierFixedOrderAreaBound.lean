import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
Every finite system of singleton and two-coordinate Fourier coefficients whose
level-one and level-two `ℓ¹` masses are at most one and whose nonconstant
Parseval mass is at most one has a fixed coordinate order with root-inclusive
completion-time area at most `3 + √2 / 2`.
-/
def quadraticFourierFixedOrderAreaBound : Prop :=
  ∀ (n : ℕ) (linear : Fin n → ℝ) (quadratic : Fin n → Fin n → ℝ),
    (∑ i, |linear i|) ≤ 1 →
    (∑ i, ∑ j ∈ Finset.Ioi i, |quadratic i j|) ≤ 1 →
    (∑ i, (linear i) ^ 2) +
        (∑ i, ∑ j ∈ Finset.Ioi i, (quadratic i j) ^ 2) ≤ 1 →
    ∃ order : Equiv.Perm (Fin n),
      (∑ i, (linear i) ^ 2 * ((((order.symm i : Fin n) : ℕ) : ℝ) + 1)) +
          (∑ i, ∑ j ∈ Finset.Ioi i,
            (quadratic i j) ^ 2 *
              max (((((order.symm i : Fin n) : ℕ) : ℝ) + 1))
                (((((order.symm j : Fin n) : ℕ) : ℝ) + 1))) ≤
        3 + Real.sqrt 2 / 2

end

end MathlibPlus.Open.Probability
