import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0613.Claim23317

noncomputable section

abbrev PositiveIndex := ℕ+
abbrev CoefficientRing := MvPolynomial PositiveIndex ℚ
abbrev RootRing := Polynomial CoefficientRing
abbrev ToricRing := MvPolynomial (Fin 2) ℚ

private def rootZ : RootRing := Polynomial.X

private def rootX (k : PositiveIndex) : RootRing :=
  Polynomial.C (MvPolynomial.X k)

private def rootClosure (P : RootRing) : RootRing :=
  rootZ * P +
    P.support.sum (fun k =>
      Polynomial.C (MvPolynomial.X (Nat.succPNat k) * P.coeff k))

private def rootStable (S : Subalgebra ℚ RootRing) : Prop :=
  ∀ P : RootRing, P ∈ S → rootClosure P ∈ S

private noncomputable def scalarAlgebra : Subalgebra ℚ RootRing :=
  sInf {S : Subalgebra ℚ RootRing | rootStable S}

private def toricU : ToricRing := MvPolynomial.X 0

private def toricV : ToricRing := MvPolynomial.X 1

private def toricCoefficientMap : CoefficientRing →+* ToricRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ToricRing)
    (fun k => toricU * toricV ^ (k : ℕ))

private def toricSpecialization : RootRing →ₐ[ℚ] ToricRing :=
  RingHom.toRatAlgHom (Polynomial.eval₂RingHom toricCoefficientMap toricV)

private def toricIdeal : Ideal CoefficientRing :=
  RingHom.ker toricCoefficientMap

private def closedPolynomial (P : RootRing) : Prop :=
  ∃ p : CoefficientRing, P = Polynomial.C p

private def closedOnly : Set RootRing :=
  {P | P ∈ scalarAlgebra ∧ closedPolynomial P}

private def constantsPlusToricIdeal : Set RootRing :=
  {P |
    ∃ q : ℚ, ∃ j : CoefficientRing,
      j ∈ toricIdeal ∧
        P = Polynomial.C (algebraMap ℚ CoefficientRing q + j)}

private def coefficientWeight (m : PositiveIndex →₀ ℕ) : ℕ :=
  m.sum (fun k a => (k : ℕ) * a)

private def weightedHomogeneous (p : CoefficientRing) (n : ℕ) : Prop :=
  ∀ m ∈ p.support, coefficientWeight m = n

private def closedOnlyPiece (n : ℕ) : Set CoefficientRing :=
  {p | Polynomial.C p ∈ scalarAlgebra ∧ weightedHomogeneous p n}

private def toricHomogeneousPiece (n : ℕ) : Set CoefficientRing :=
  {p | p ∈ toricIdeal ∧ weightedHomogeneous p n}

/-- Claim 23317: the closed part of the rooted-factor algebra is the
constant summand together with the rank-one toric ideal, and its positive
weighted pieces are exactly the corresponding homogeneous ideal pieces. -/
def claim23317 : Prop :=
  closedOnly = constantsPlusToricIdeal ∧
    Polynomial.C (1 : CoefficientRing) ∈ scalarAlgebra ∧
    ∀ n : ℕ, 0 < n → closedOnlyPiece n = toricHomogeneousPiece n

end

end MathlibPlus.Open.ResearchFormalization.R0613.Claim23317
