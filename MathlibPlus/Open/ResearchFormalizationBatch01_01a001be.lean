import Mathlib
import MathlibPlus.Algebra.LinearQuadraticFactorization
import MathlibPlus.Algebra.CoefficientResultantJacobian

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

namespace Claim7131

abbrev PrimeIndex (n : ℕ) := {p : ℕ // p ∈ (Nat.factorization n).support}
abbrev TensorIndex (n : ℕ) := ∀ p : PrimeIndex n, Fin (Nat.factorization n p.1 + 1)
abbrev StateSpace (n : ℕ) := TensorIndex n → ℂ

def exponent (n : ℕ) (p : PrimeIndex n) : ℕ := Nat.factorization n p.1

def exponentDifference (n : ℕ) (i : TensorIndex n) (p : PrimeIndex n) : ℤ :=
  (exponent n p : ℤ) - 2 * (i p).val

def weight (n : ℕ) (i : TensorIndex n) : ℝ :=
  ∑ p : PrimeIndex n,
    (exponentDifference n i p : ℝ) * Real.log p.1

def reverseIndex (n : ℕ) (i : TensorIndex n) : TensorIndex n :=
  fun p => ⟨exponent n p - (i p).val, by
    have hsub : exponent n p - (i p).val ≤ exponent n p := Nat.sub_le _ _
    exact Nat.lt_succ_of_le hsub⟩

def middleIndex (n : ℕ) : TensorIndex n :=
  fun p => ⟨exponent n p / 2, by
    have hdiv : exponent n p / 2 ≤ exponent n p := Nat.div_le_self _ _
    exact Nat.lt_succ_of_le hdiv⟩

def tensorBasis (n : ℕ) (i : TensorIndex n) : StateSpace n :=
  fun j => if j = i then 1 else 0

def cartan (n : ℕ) : StateSpace n →ₗ[ℂ] StateSpace n :=
  { toFun := fun v i => Complex.ofReal (weight n i) * v i
    map_add' := by
      intro v w
      funext i
      simp [mul_add]
    map_smul' := by
      intro c v
      funext i
      simp [mul_assoc, mul_comm] }

def reversal (n : ℕ) : StateSpace n →ₗ[ℂ] StateSpace n :=
  { toFun := fun v i => v (reverseIndex n i)
    map_add' := by
      intro v w
      rfl
    map_smul' := by
      intro c v
      rfl }

def squareNatural (n : ℕ) : Prop := ∃ m : ℕ, m ^ 2 = n

def squareSupportKernelClaim : Prop :=
  ∀ n : ℕ, 1 < n →
    (∀ i : TensorIndex n,
      weight n i = 0 ↔ ∀ p : PrimeIndex n, exponentDifference n i p = 0) ∧
    ((¬ squareNatural n → LinearMap.ker (cartan n) = ⊥) ∧
      (squareNatural n →
        LinearMap.ker (cartan n) =
            Submodule.span ℂ {tensorBasis n (middleIndex n)} ∧
          Module.finrank ℂ (LinearMap.ker (cartan n)) = 1 ∧
          reversal n (tensorBasis n (middleIndex n)) =
            tensorBasis n (middleIndex n) ∧
          ∀ v, v ∈ LinearMap.ker (cartan n) → reversal n v = v))

end Claim7131

namespace Claim7149

abbrev Coordinate (m : ℕ) := Fin m → ℂ

def rho (a b c d e : ℂ) : ℂ := a ^ 2 * e - a * b * d + c * b ^ 2

def linearForm (a b : ℂ) : Polynomial ℂ :=
  Polynomial.C a * Polynomial.X + Polynomial.C b

def quadraticForm (c d e : ℂ) : Polynomial ℂ :=
  Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d * Polynomial.X + Polynomial.C e

def coefficientProduct (a b c d e : ℂ) : Polynomial ℂ :=
  linearForm a b * quadraticForm c d e

def coefficientResultantMap (a b c d e : ℂ) : Coordinate 5 :=
  ![a * c, a * d + b * c, a * e + b * d, b * e, rho a b c d e]

def multiplicationDifferential (a b c d e : ℂ) (u : Coordinate 2) (v : Coordinate 3) : Coordinate 4 :=
  ![u 0 * c + a * v 0,
    u 0 * d + u 1 * c + a * v 1 + b * v 0,
    u 0 * e + u 1 * d + a * v 2 + b * v 1,
    u 1 * e + b * v 2]

def relativeResultantPath (a b c d e t : ℂ) : ℂ :=
  rho (a + t * a) (b + t * b) (c - t * c) (d - t * d) (e - t * e)

def jacobian (a b c d e : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![ c, 0, a, 0, 0;
      d, c, b, a, 0;
      e, d, 0, b, a;
      0, e, 0, 0, b;
      2 * a * e - b * d, 2 * b * c - a * d, b ^ 2, -a * b, a ^ 2 ]

abbrev CoordinatePolynomialRing := MvPolynomial (Fin 5) ℂ

def rhoPolynomial : CoordinatePolynomialRing :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 4 -
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
      MvPolynomial.X 2 * MvPolynomial.X 1 ^ 2

def coefficientResultantCoordinatePolynomials : Fin 5 → CoordinatePolynomialRing :=
  ![MvPolynomial.X 0 * MvPolynomial.X 2,
    MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2,
    MvPolynomial.X 0 * MvPolynomial.X 4 + MvPolynomial.X 1 * MvPolynomial.X 3,
    MvPolynomial.X 1 * MvPolynomial.X 4,
    rhoPolynomial]

def coefficientResultantRingHom : CoordinatePolynomialRing →+* CoordinatePolynomialRing :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ℂ →+* CoordinatePolynomialRing)
    coefficientResultantCoordinatePolynomials

noncomputable def localizedCoefficientResultantRingHom :
    Localization.Away (MvPolynomial.X (R := ℂ) (4 : Fin 5)) →+*
      Localization.Away rhoPolynomial := by
  let f := coefficientResultantRingHom
  have h : f (MvPolynomial.X (R := ℂ) (4 : Fin 5)) = rhoPolynomial := by
    simp [f, coefficientResultantRingHom,
      coefficientResultantCoordinatePolynomials, rhoPolynomial]
  letI : IsLocalization.Away
      (f (MvPolynomial.X (R := ℂ) (4 : Fin 5)))
      (Localization.Away rhoPolynomial) := h ▸ inferInstance
  exact IsLocalization.Away.map
    (Localization.Away (MvPolynomial.X (R := ℂ) (4 : Fin 5)))
    (Localization.Away rhoPolynomial)
    f (MvPolynomial.X (R := ℂ) (4 : Fin 5))

def coefficientResultantMapIsEtaleOn : Prop :=
  RingHom.Etale localizedCoefficientResultantRingHom

def differentialKernelAndEtaleClaim : Prop :=
  coefficientResultantMapIsEtaleOn ∧
    ∀ a b c d e : ℂ,
      rho a b c d e ≠ 0 →
        IsCoprime (linearForm a b) (quadraticForm c d e) ∧
        (∀ u : Coordinate 2, ∀ v : Coordinate 3,
          multiplicationDifferential a b c d e u v = 0 ↔
            ∃ l : ℂ,
              u = ![l * a, l * b] ∧
              v = ![-l * c, -l * d, -l * e]) ∧
        HasDerivAt (fun t : ℂ => relativeResultantPath a b c d e t)
          (rho a b c d e) 0 ∧
        rho a b c d e ≠ 0 ∧
        IsUnit (Matrix.det (jacobian a b c d e))

end Claim7149

end

end MathlibPlus.Open.ResearchFormalizationBatch

