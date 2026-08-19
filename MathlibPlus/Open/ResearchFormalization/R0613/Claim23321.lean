import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0613.Repair

noncomputable section

abbrev PositiveIndex := ℕ+
abbrev CoefficientRing := MvPolynomial PositiveIndex ℚ
abbrev RootRing := Polynomial CoefficientRing
abbrev ToricRing := MvPolynomial (Fin 2) ℚ

private def positiveOne : PositiveIndex := 1

private def rootZ : RootRing := Polynomial.X

private def rootX (k : PositiveIndex) : RootRing :=
  Polynomial.C (MvPolynomial.X k)

private def rootClosure (P : RootRing) : RootRing :=
  rootZ * P +
    P.support.sum (fun k =>
      Polynomial.C (MvPolynomial.X (Nat.succPNat k) * P.coeff k))

private def rootStable (S : Subalgebra ℚ RootRing) : Prop :=
  ∀ P : RootRing, P ∈ S → rootClosure P ∈ S

private def scalarAlgebra : Subalgebra ℚ RootRing :=
  sInf {S : Subalgebra ℚ RootRing | rootStable S}

private def toricU : ToricRing := MvPolynomial.X 0

private def toricV : ToricRing := MvPolynomial.X 1

private def toricCoefficientMap : CoefficientRing →+* ToricRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ToricRing)
    (fun k => toricU * toricV ^ (k : ℕ))

private def toricSpecialization : RootRing →ₐ[ℚ] ToricRing :=
  RingHom.toRatAlgHom (Polynomial.eval₂RingHom toricCoefficientMap toricV)

private def scalarS : RootRing := rootZ + rootX positiveOne

private def scalarW : ToricRing := toricV * (1 + toricU)

private def scalarLine : Subalgebra ℚ ToricRing :=
  Algebra.adjoin ℚ ({scalarW} : Set ToricRing)

private def scalarPreimage : Subalgebra ℚ RootRing :=
  Subalgebra.comap toricSpecialization scalarLine

private def scalarFiberProduct : Subalgebra ℚ (RootRing × scalarLine) :=
  AlgHom.pullback toricSpecialization scalarLine.val

private def scalarLineInRoot : Subalgebra ℚ RootRing :=
  Algebra.adjoin ℚ ({scalarS} : Set RootRing)

private def phiKernel : Submodule ℚ RootRing :=
  LinearMap.ker toricSpecialization.toLinearMap

private def vectorSpaceDirectSum
    (U V W : Submodule ℚ RootRing) : Prop :=
  U ⊔ V = W ∧ Disjoint U V

private def coefficientWeight (m : PositiveIndex →₀ ℕ) : ℕ :=
  m.sum (fun k a => (k : ℕ) * a)

private def rootMonomialWeight (zDegree : ℕ)
    (m : PositiveIndex →₀ ℕ) : ℕ :=
  zDegree + coefficientWeight m

private def weightedHomogeneous (P : RootRing) (n : ℕ) : Prop :=
  ∀ a ∈ P.support, ∀ m ∈ (P.coeff a).support,
    rootMonomialWeight a m = n

private def weightPiece (n : ℕ) : Submodule ℚ RootRing :=
  Submodule.span ℚ {P : RootRing | weightedHomogeneous P n}

private def scalarPiece (n : ℕ) : Submodule ℚ RootRing :=
  scalarAlgebra.toSubmodule ⊓ weightPiece n

private def closedPolynomialSubmodule : Submodule ℚ RootRing :=
  Submodule.span ℚ {P : RootRing | P.support ⊆ ({0} : Finset ℕ)}

private def closedOnlyPiece (n : ℕ) : Submodule ℚ RootRing :=
  scalarPiece n ⊓ closedPolynomialSubmodule

private def fullScalarDimension (n : ℕ) : ℕ :=
  Module.finrank ℚ (scalarPiece n)

private def positiveScalarDimension (n : ℕ) : ℕ :=
  fullScalarDimension n - Module.finrank ℚ (closedOnlyPiece n)

private def closedOnlyPositiveDimension (n : ℕ) : ℕ :=
  Module.finrank ℚ (closedOnlyPiece n)

private abbrev TriangularIndex := {k : PositiveIndex // 2 ≤ (k : ℕ)}

private def scalarE (k : TriangularIndex) : RootRing :=
  rootX k.1 - rootZ ^ ((k : ℕ) - 1) * rootX positiveOne

private def eWeight (m : TriangularIndex →₀ ℕ) : ℕ :=
  m.sum (fun k a => (k : ℕ) * a)

private def eProduct (m : TriangularIndex →₀ ℕ) : RootRing :=
  m.prod (fun k a => scalarE k ^ a)

private structure KernelMonomialIndex (n : ℕ) where
  zExponent : ℕ
  xExponent : ℕ
  eExponents : TriangularIndex →₀ ℕ
  weight_eq : zExponent + xExponent + eWeight eExponents = n
  has_e_factor : eExponents.support.Nonempty

private abbrev ScalarBasisIndex (n : ℕ) := Option (KernelMonomialIndex n)

private def scalarBasisVector {n : ℕ} : ScalarBasisIndex n → RootRing
  | none => scalarS ^ n
  | some q =>
      rootZ ^ q.zExponent * rootX positiveOne ^ q.xExponent *
        eProduct q.eExponents



private def positiveIndexAt (d : ℕ) (hd : 2 ≤ d) : PositiveIndex :=
  ⟨d, Nat.zero_lt_of_lt hd⟩

private def triangularIndexAt (d : ℕ) (hd : 2 ≤ d) : TriangularIndex :=
  ⟨positiveIndexAt d hd, hd⟩

private noncomputable def deltaNat (d : ℕ) : RootRing :=
  if hd : 2 ≤ d then scalarE (triangularIndexAt d hd) else 0

/-- The binomial triangular identity and its inductive extraction of every
higher delta generator into the smallest root-stable scalar algebra. -/
def starDeviationTriangularExtraction_claim23321 : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    rootClosure (scalarS ^ (d - 1)) - scalarS ^ d ∈ scalarAlgebra ∧
    rootClosure (scalarS ^ (d - 1)) - scalarS ^ d =
      deltaNat d +
        (Finset.sum (Finset.Icc 2 (d - 1)) (fun j =>
          algebraMap ℚ RootRing (Nat.choose (d - 1) (j - 1) : ℚ) *
            rootX positiveOne ^ (d - j) * deltaNat j)) ∧
    deltaNat d ∈ scalarAlgebra

end

end MathlibPlus.Open.ResearchFormalization.R0613.Repair
