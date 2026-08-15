import Mathlib

namespace MathlibPlus.Open

/--
Shape-preserving level-wise gauges for a nonnegative graded up-down relation
have a constant transformed parameter precisely when the successive gamma
ratios are constant; in that case the exact relation-data orbit is the stated
one, and all orbit parameters are realized by level scalars.
-/
def shapePreservingGaugeOrbit_5021 : Prop :=
  ∀ (K : Type*) [Field K]
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    [∀ n, Module K (A n)]
    [∀ n, FiniteDimensional K (A n)]
    (U : ∀ n : ℕ, A n →ₗ[K] A (n + 1))
    (D : ∀ n : ℕ, A (n + 1) →ₗ[K] A n)
    (q : Kˣ)
    (r : ℕ → K),
    ((D 0).comp (U 0) =
        (r 0) • (LinearMap.id : A 0 →ₗ[K] A 0)) ∧
      (∀ n : ℕ,
        (D (n + 1)).comp (U (n + 1)) -
            (q : K) • (U n).comp (D n) =
          (r (n + 1)) •
            (LinearMap.id : A (n + 1) →ₗ[K] A (n + 1))) →
    ∀ (a b : ℕ → Kˣ),
      let gamma : ℕ → Kˣ := fun n => b (n + 1) * a n
      let U' : ∀ n : ℕ, A n →ₗ[K] A (n + 1) :=
        fun n => (a n : K) • U n
      let D' : ∀ n : ℕ, A (n + 1) →ₗ[K] A n :=
        fun n => (b (n + 1) : K) • D n
      let ratio : ℕ → Kˣ := fun n => gamma (n + 1) / gamma n
      let transformedQ : ℕ → Kˣ := fun n => q * ratio n
      let transformedR : ℕ → K := fun n => (gamma n : K) * r n
      ((∃ qtilde : Kˣ, ∀ n : ℕ, transformedQ n = qtilde) ↔
          (∃ c : Kˣ, ∀ n : ℕ, ratio n = c)) ∧
        (∀ c : Kˣ, (∀ n : ℕ, ratio n = c) →
          (∀ n : ℕ, gamma n = gamma 0 * c ^ n) ∧
          (∀ n : ℕ, transformedQ n = c * q) ∧
          (∀ n : ℕ, transformedR n =
            ((gamma 0 * c ^ n : Kˣ) : K) * r n) ∧
          (D' 0).comp (U' 0) =
            transformedR 0 • (LinearMap.id : A 0 →ₗ[K] A 0) ∧
          (∀ n : ℕ,
            (D' (n + 1)).comp (U' (n + 1)) -
                ((c * q : Kˣ) : K) • (U' n).comp (D' n) =
              transformedR (n + 1) •
                (LinearMap.id : A (n + 1) →ₗ[K] A (n + 1)))) ∧
        (∀ c gamma0 : Kˣ, ∃ a0 b0 : ℕ → Kˣ,
          let gamma0' : ℕ → Kˣ := fun n => b0 (n + 1) * a0 n
          let U0' : ∀ n : ℕ, A n →ₗ[K] A (n + 1) :=
            fun n => (a0 n : K) • U n
          let D0' : ∀ n : ℕ, A (n + 1) →ₗ[K] A n :=
            fun n => (b0 (n + 1) : K) • D n
          (∀ n : ℕ, gamma0' n = gamma0 * c ^ n) ∧
          (∀ n : ℕ, q * (gamma0' (n + 1) / gamma0' n) = c * q) ∧
          (∀ n : ℕ, (gamma0' n : K) * r n =
            ((gamma0 * c ^ n : Kˣ) : K) * r n) ∧
          (D0' 0).comp (U0' 0) =
            (((gamma0 : Kˣ) : K) * r 0) •
              (LinearMap.id : A 0 →ₗ[K] A 0) ∧
          (∀ n : ℕ,
            (D0' (n + 1)).comp (U0' (n + 1)) -
                ((c * q : Kˣ) : K) • (U0' n).comp (D0' n) =
              (((gamma0 * c ^ (n + 1) : Kˣ) : K) * r (n + 1)) •
                (LinearMap.id : A (n + 1) →ₗ[K] A (n + 1))))

end MathlibPlus.Open
