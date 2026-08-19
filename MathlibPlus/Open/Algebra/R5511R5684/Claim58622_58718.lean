import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.R5511R5684

/-- Claim 58622: a fixed linear map carries every signed scalar circuit of
ordinary coefficient vectors to a signed scalar circuit. -/
def fixedScalarLinearTransformPreservesCircuits_claim58622 : Prop :=
  ∀ (R V W : Type*) [Semiring R]
    [AddCommMonoid V] [AddCommMonoid W]
    [Module R V] [Module R W]
    (L : V →ₗ[R] W) (r : ℕ)
    (ε : Fin r → R) (u : Fin r → V),
    (∑ i : Fin r, ε i • u i = 0) →
      ∑ i : Fin r, ε i • L (u i) = 0

noncomputable def midpointKernel
    {n : ℕ} (m : ℤ) (v : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j =>
    (if i = j then (m : ℚ) * (v i : ℚ) else 0) -
      (v i : ℚ) * (v j : ℚ)

noncomputable def midpointOuterDifference
    {n : ℕ} (a c : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (a i - c i : ℚ) * (a j - c j : ℚ)

/-- Claim 58718: the exact integer-midpoint covariance identity and its
nonzero rank-one midpoint direction. -/
def covarianceMidpointIdentity_claim58718 : Prop :=
  ∀ (n : ℕ) (m : ℤ) (a b c : Fin n → ℤ),
    (∑ i : Fin n, a i) = m ∧
      (∑ i : Fin n, c i) = m ∧
      (∀ i : Fin n, 2 * b i = a i + c i) →
      midpointKernel m a + midpointKernel m c - 2 • midpointKernel m b =
        (-1 / 2 : ℚ) • midpointOuterDifference a c ∧
        (a ≠ c →
          ∃ i j : Fin n,
            ((-1 / 2 : ℚ) • midpointOuterDifference a c) i j ≠ 0)

end MathlibPlus.Open.Algebra.R5511R5684
