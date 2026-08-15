import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

/--
A graded up-down pair for the normalized commutator claim from source group D-0076.
The `ℤ`-indexed family records the vanishing negative levels; `U n` and `D n`
are the maps `U_n : A_n → A_{n+1}` and `D_{n+1} : A_{n+1} → A_n`.
-/
def gradedUpDownPair_D0076
    (K : Type*) [Field K]
    (A : ℤ → Type*)
    [∀ n : ℤ, AddCommGroup (A n)]
    [∀ n : ℤ, Module K (A n)]
    (U : ∀ n : ℤ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℤ, A (n + 1) →ₗ[K] A n)
    (q : Kˣ)
    (r : ℕ → K) : Prop :=
  (∀ n : ℤ, FiniteDimensional K (A n)) ∧
    (∀ n : ℤ, n < 0 → ∀ x : A n, x = 0) ∧
    (D 0 ∘ₗ U 0 =
      (r 0) • (LinearMap.id : A 0 →ₗ[K] A 0)) ∧
    (∀ n : ℕ,
      D ((n : ℤ) + 1) ∘ₗ U ((n : ℤ) + 1) -
          (q : K) • (U (n : ℤ) ∘ₗ D (n : ℤ)) =
        r (n + 1) •
          (LinearMap.id : A ((n : ℤ) + 1) →ₗ[K] A ((n : ℤ) + 1)))

/--
Normalized commutator form: for a graded up-down pair, if every `r n` is
nonzero, the gauge parameters `c = q⁻¹` and `γ₀ = r₀⁻¹` give `q̃ = 1`,
`r̃₀ = 1`, and the normalized level commutator has coefficient
`ρ n = ∏ j in [1,n], λ j`, where
`λ j = r j / (q r (j - 1))` for positive `j`.
-/
def normalizedCommutatorForm_D0076
    (K : Type*) [Field K]
    (A : ℤ → Type*)
    [∀ n : ℤ, AddCommGroup (A n)]
    [∀ n : ℤ, Module K (A n)]
    (U : ∀ n : ℤ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℤ, A (n + 1) →ₗ[K] A n)
    (q : Kˣ)
    (r : ℕ → K) : Prop :=
  gradedUpDownPair_D0076 K A U D q r →
    (∀ hnonzero : ∀ n : ℕ, r n ≠ 0,
      let c : Kˣ := q⁻¹
      let gammaZero : Kˣ := (Units.mk0 (r 0) (hnonzero 0))⁻¹
      let gamma : ℕ → K :=
        fun n => (gammaZero : K) * (c : K) ^ n
      let qtilde : Kˣ := c * q
      let rtilde : ℕ → K := fun n => gamma n * r n
      let lambda : ℕ → K := fun j =>
        if 0 < j then r j / ((q : K) * r (j - 1)) else 1
      let rho : ℕ → K := fun n =>
        ∏ j ∈ Finset.Icc 1 n, lambda j
      (qtilde = (1 : Kˣ)) ∧
        (rtilde 0 = 1) ∧
        (∀ n : ℕ, rtilde n = rho n) ∧
        (D 0 ∘ₗ (gamma 0 • U 0) =
          rho 0 • (LinearMap.id : A 0 →ₗ[K] A 0)) ∧
        (∀ n : ℕ,
          D ((n : ℤ) + 1) ∘ₗ (gamma (n + 1) • U ((n : ℤ) + 1)) -
              (qtilde : K) •
                ((gamma n • U (n : ℤ)) ∘ₗ D (n : ℤ)) =
            rho (n + 1) •
              (LinearMap.id : A ((n : ℤ) + 1) →ₗ[K] A ((n : ℤ) + 1))))

end MathlibPlus.Open.Research
