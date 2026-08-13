import Mathlib

namespace MathlibPlus.Analysis.Claim8027

/-- Exact carrier for a finite confluent exponential-polynomial sequence.
The index type `Fin J` makes the family finite; `x` records the distinct,
nonzero bases, `P` the polynomial blocks, and `m` their multiplicities. -/
def IsFiniteConfluentExponentialPolynomial
    {R : Type*} [CommRing R]
    (s : ℕ → R) (J : ℕ)
    (P : Fin J → Polynomial R) (x : Fin J → R) (m : Fin J → ℕ) : Prop :=
  (∀ j, x j ≠ 0) ∧
    (∀ ⦃i j⦄, i ≠ j → x i ≠ x j) ∧
    (∀ j, 0 < m j ∧
      (P j).natDegree = m j - 1 ∧
      (P j).leadingCoeff ≠ 0) ∧
    (∀ n, s n = ∑ j, (P j).eval (n : R) * (x j) ^ n)

end MathlibPlus.Analysis.Claim8027
