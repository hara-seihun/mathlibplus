import Mathlib

namespace MathlibPlus.Open

/--
Claim 5019: level-wise grading gauge. Integer-indexed levels make the
negative levels in the admitted graded up-down-pair context explicit; the
scalars and the displayed gauge are indexed by the nonnegative levels.
-/
def levelWiseGradingGauge_5019 : Prop :=
  ∀ (K : Type*) [Field K]
    (A : ℤ → Type*)
    [∀ n : ℤ, AddCommGroup (A n)]
    [∀ n : ℤ, Module K (A n)]
    (_finite_levels : ∀ n : ℕ, FiniteDimensional K (A (n : ℤ)))
    (_negative_levels_zero :
      ∀ n : ℤ, n < 0 → ∀ x : A n, x = 0)
    (U : ∀ n : ℤ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℤ, A n →ₗ[K] A (n - 1))
    (q : Kˣ)
    (r : ℕ → K),
    (∀ n : ℕ,
      let dn1 : A ((n : ℤ) + 1) →ₗ[K] A (n : ℤ) :=
        (LinearEquiv.cast (Int.add_sub_cancel (n : ℤ) 1)).toLinearMap.comp
          (D ((n : ℤ) + 1))
      let unm1 : A ((n : ℤ) - 1) →ₗ[K] A (n : ℤ) :=
        (LinearEquiv.cast (Int.sub_add_cancel (n : ℤ) 1)).toLinearMap.comp
          (U ((n : ℤ) - 1))
      dn1.comp (U (n : ℤ)) -
          (q : K) • unm1.comp (D (n : ℤ)) =
        (r n) • LinearMap.id) →
      ∀ (a b : ℕ → K),
        (∀ n : ℕ, a n ≠ 0) →
          (∀ n : ℕ, b n ≠ 0) →
            ∃ (U_tilde : ∀ n : ℕ,
                A (n : ℤ) →ₗ[K] A ((n : ℤ) + 1))
              (D_tilde : ∀ n : ℕ,
                A (n : ℤ) →ₗ[K] A ((n : ℤ) - 1))
              (gamma : ℕ → K),
              (∀ n : ℕ,
                U_tilde n = (a n) • U (n : ℤ)) ∧
                (∀ n : ℕ,
                  D_tilde n = (b n) • D (n : ℤ)) ∧
                  (∀ n : ℕ, gamma n = b (n + 1) * a n)

end MathlibPlus.Open
