import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AdmittedBatch

noncomputable section

/-- Lehmer's polynomial. -/
def lehmerPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 - Polynomial.X ^ 6 -
    Polynomial.X ^ 5 - Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X + 1

/-- The substitution family `L(x^K)`. -/
def lehmerSubstitution (K : ℕ) : Polynomial ℤ :=
  lehmerPolynomial.comp (Polynomial.X ^ K)

/-- Mahler measure, written using the complex roots with multiplicity. -/
def polynomialMahlerMeasure (p : Polynomial ℤ) : ℝ :=
  ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ *
    Multiset.prod
      ((p.map (Int.castRingHom ℂ)).roots.map (fun z => max 1 ‖z‖))

/-- The roots above `α`, including their lift multiplicity and modulus. -/
def lehmerRootLifts (K : ℕ) (α : ℂ) : Prop :=
  ∃ β : Fin K → ℂ,
    Function.Injective β ∧
      (∀ i : Fin K,
        β i ^ K = α ∧
          Polynomial.IsRoot
            ((lehmerSubstitution K).map (Int.castRingHom ℂ)) (β i) ∧
          ‖β i‖ = Real.rpow ‖α‖ (1 / (K : ℝ))) ∧
      (∀ z : ℂ, z ^ K = α → ∃ i : Fin K, β i = z)

/-- The named Mahler measure in the admitted construction. -/
def lehmerTau : ℝ := polynomialMahlerMeasure lehmerPolynomial

/-- Claim 57289: the explicit reciprocal Lehmer substitution family. -/
def lehmerSubstitutionFamily : Prop :=
  ∀ (K : ℕ), 1 ≤ K →
    (lehmerSubstitution K).natDegree = 10 * K ∧
      (lehmerPolynomial.reverse = lehmerPolynomial →
        (lehmerSubstitution K).reverse = lehmerSubstitution K) ∧
      (∀ α : ℂ,
        Polynomial.IsRoot (lehmerPolynomial.map (Int.castRingHom ℂ)) α →
          lehmerRootLifts K α)

/-- Claim 57292: the cyclic and primitive resultant plateaux. -/
def lehmerResultantPlateau : Prop :=
  ∀ (K m : ℕ), 1 ≤ K → m ∣ K →
    (lehmerSubstitution K).natDegree = 10 * K ∧
      Even (lehmerSubstitution K).natDegree ∧
      (∀ ζ : ℂ, ζ ^ m = 1 →
        ζ ^ K = 1 ∧
          Polynomial.eval ζ ((lehmerSubstitution K).map (Int.castRingHom ℂ)) =
            Polynomial.eval 1 (lehmerPolynomial.map (Int.castRingHom ℂ)) ∧
          Polynomial.eval 1 (lehmerPolynomial.map (Int.castRingHom ℂ)) = -1) ∧
      Polynomial.resultant (lehmerSubstitution K)
          (Polynomial.X ^ m - 1) = (-1 : ℤ) ^ m ∧
      Polynomial.resultant (lehmerSubstitution K)
          (Polynomial.cyclotomic m ℤ) = (-1 : ℤ) ^ Nat.totient m ∧
      Int.natAbs
          (Polynomial.resultant (lehmerSubstitution K)
            (Polynomial.X ^ m - 1)) = 1 ∧
      Int.natAbs
          (Polynomial.resultant (lehmerSubstitution K)
            (Polynomial.cyclotomic m ℤ)) = 1

end

end MathlibPlus.Open.AdmittedBatch
