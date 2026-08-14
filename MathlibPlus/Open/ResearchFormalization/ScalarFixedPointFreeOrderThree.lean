import Mathlib

namespace MathlibPlus.Open
namespace ResearchFormalization

/-- Every Sylow subgroup has exponent dividing its prime, hence is elementary abelian. -/
def hasElementaryAbelianSylow (M : Type*) [Finite M] [CommGroup M] : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∀ P : Sylow p M, ∀ x : P, x ^ p = 1

/-- The scalar condition from the fixed-point-free order-three action statement. -/
def scalarFixedPointFreeOrderThree (M : Type*) [Finite M] [CommGroup M] : Prop :=
  ∃ ell : ℤ,
    Int.ModEq (Monoid.exponent M : ℤ) (ell ^ 3) 1 ∧
      Int.gcd (ell * (ell - 1)) (Monoid.exponent M : ℤ) = 1

/-- The prime-divisor condition on the exponent. -/
def exponentPrimeDivisorsAreOneModThree
    (M : Type*) [Finite M] [CommGroup M] : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ Monoid.exponent M → Nat.ModEq 3 q 1

/--
A concrete finite product of elementary abelian prime groups. Repeated indices
allow arbitrary finite dimensions, and `n = 0` is the trivial empty product.
-/
def productOfElementaryAbelianPrimeModThreeGroups
    (M : Type*) [Finite M] [CommGroup M] : Prop :=
  ∃ n : ℕ, ∃ q : Fin n → ℕ,
    (∀ i : Fin n, Nat.Prime (q i) ∧ Nat.ModEq 3 (q i) 1) ∧
      Nonempty (M ≃* (∀ i : Fin n, Multiplicative (ZMod (q i))))

/--
A finite abelian group with elementary abelian Sylow subgroups admits the
fixed-point-free scalar of order three exactly under the stated prime
condition, equivalently exactly when it has the stated product form.
-/
def scalarFixedPointFreeOrderThreeActionDomain
    (M : Type*) [Finite M] [CommGroup M] : Prop :=
  hasElementaryAbelianSylow M →
    (scalarFixedPointFreeOrderThree M ↔ exponentPrimeDivisorsAreOneModThree M) ∧
      (exponentPrimeDivisorsAreOneModThree M ↔
        productOfElementaryAbelianPrimeModThreeGroups M)

/-- A nonzero, nonidentity cube root of one modulo a prime. -/
def nonzeroNonidentityCubeRoot (q : ℕ) : Prop :=
  ∃ r : ZMod q, r ^ 3 = 1 ∧ r ≠ 0 ∧ r ≠ 1

/-- The prime-by-prime local cube-root condition at the exponent primes. -/
def exponentPrimeDivisorsHaveNonzeroNonidentityCubeRoots
    (M : Type*) [Finite M] [CommGroup M] : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ Monoid.exponent M → nonzeroNonidentityCubeRoot q

/--
Square-freeness of the exponent together with the local cube-root
characterization and the CRT converse scalar described in the admitted claim.
-/
def elementarySylowSquarefreeScalarCRT
    (M : Type*) [Finite M] [CommGroup M] : Prop :=
  hasElementaryAbelianSylow M →
    Squarefree (Monoid.exponent M) ∧
      (∀ q : ℕ, Nat.Prime q →
        (nonzeroNonidentityCubeRoot q ↔ Nat.ModEq 3 q 1)) ∧
      (scalarFixedPointFreeOrderThree M ↔
        exponentPrimeDivisorsHaveNonzeroNonidentityCubeRoots M)

end ResearchFormalization
end MathlibPlus.Open
