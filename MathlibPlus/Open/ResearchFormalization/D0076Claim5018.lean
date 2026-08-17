import MathlibPlus.Open.LevelWiseGradingGauge5019

namespace MathlibPlus.Open.ResearchFormalization.D0076Claim5018

/-- The graded up-down pair predicate with the reviewed integer-indexed graded
carrier and its cast-corrected commutator relation. -/
def gradedUpDownPair_claim5018
    (K : Type*) [Field K]
    (A : ℤ → Type*)
    [∀ n : ℤ, AddCommGroup (A n)]
    [∀ n : ℤ, Module K (A n)]
    (U : ∀ n : ℤ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℤ, A n →ₗ[K] A (n - 1))
    (q : Kˣ)
    (r : ℕ → K) : Prop :=
  (∀ n : ℕ, FiniteDimensional K (A (n : ℤ))) ∧
    (∀ n : ℤ, n < 0 → ∀ x : A n, x = 0) ∧
    (∀ n : ℕ,
      let dn1 : A ((n : ℤ) + 1) →ₗ[K] A (n : ℤ) :=
        (LinearEquiv.cast (Int.add_sub_cancel (n : ℤ) 1)).toLinearMap.comp
          (D ((n : ℤ) + 1))
      let unm1 : A ((n : ℤ) - 1) →ₗ[K] A (n : ℤ) :=
        (LinearEquiv.cast (Int.sub_add_cancel (n : ℤ) 1)).toLinearMap.comp
          (U ((n : ℤ) - 1))
      dn1.comp (U (n : ℤ)) -
          (q : K) • unm1.comp (D (n : ℤ)) =
        (r n) • LinearMap.id)

end MathlibPlus.Open.ResearchFormalization.D0076Claim5018
