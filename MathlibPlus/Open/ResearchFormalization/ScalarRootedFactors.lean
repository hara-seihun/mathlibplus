import Mathlib


open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/- The concrete polynomial model used by the statements below.  The
   coefficient variable `k` denotes the informal variable `x_(k+1)`. -/
abbrev CoefficientRing := MvPolynomial ℕ ℚ
abbrev RootRing := Polynomial CoefficientRing
abbrev ToricRing := MvPolynomial (Fin 2) ℚ

def rootZ : RootRing := Polynomial.X

def coefficientVariable (k : ℕ) : CoefficientRing := MvPolynomial.X k

def rootX (k : ℕ) : RootRing := Polynomial.C (coefficientVariable (k - 1))

def rootClosure (P : RootRing) : RootRing :=
  Polynomial.X * P +
    P.support.sum (fun k => Polynomial.C (coefficientVariable k * P.coeff k))

def rootStable (S : Subalgebra ℚ RootRing) : Prop :=
  ∀ P : RootRing, P ∈ S → rootClosure P ∈ S

def scalarRootedFactorAlgebra : Subalgebra ℚ RootRing :=
  sInf {S : Subalgebra ℚ RootRing | rootStable S}

def toricU : ToricRing := MvPolynomial.X 0

def toricV : ToricRing := MvPolynomial.X 1

def toricCoefficientMap : CoefficientRing →+* ToricRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ToricRing)
    (fun k => toricU * toricV ^ (k + 1))

def toricSpecialization : RootRing →ₐ[ℚ] ToricRing :=
  RingHom.toRatAlgHom (Polynomial.eval₂RingHom toricCoefficientMap toricV)

def scalarS : RootRing := rootZ + rootX 1

def scalarW : ToricRing := toricV * (1 + toricU)

def scalarImageSubalgebra : Subalgebra ℚ ToricRing :=
  Algebra.adjoin ℚ {scalarW}

def scalarPreimage : Subalgebra ℚ RootRing :=
  Subalgebra.comap toricSpecialization scalarImageSubalgebra

def triangularDifference (k : ℕ) : RootRing :=
  rootX k - rootZ ^ (k - 1) * rootX 1

def triangularIndex := {k : ℕ // 2 ≤ k}

def coordinateGenerators : Set RootRing :=
  insert rootZ (insert (rootX 1)
    (Set.range (fun k : triangularIndex => triangularDifference k.1)))

def coordinateSubalgebra : Subalgebra ℚ RootRing :=
  Algebra.adjoin ℚ coordinateGenerators

def coordinateIndex := Sum (Fin 2) triangularIndex

def coordinateVariable : coordinateIndex → RootRing
  | Sum.inl i => if i = 0 then rootZ else rootX 1
  | Sum.inr k => triangularDifference k.1

def coefficientMonomialWeight (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun i a => (i + 1) * a)

def rootMonomialWeight (zDegree : ℕ) (m : ℕ →₀ ℕ) : ℕ :=
  zDegree + coefficientMonomialWeight m

def weightedHomogeneous (P : RootRing) (n : ℕ) : Prop :=
  ∀ a ∈ P.support, ∀ m ∈ (P.coeff a).support,
    rootMonomialWeight a m = n

def kernelIdeal : Ideal RootRing := RingHom.ker toricSpecialization.toRingHom

def kernelSubmodule : Submodule ℚ RootRing := kernelIdeal.restrictScalars ℚ

def scalarSubalgebra : Subalgebra ℚ RootRing :=
  Algebra.adjoin ℚ {scalarS}

def evaluateAtScalar (f : Polynomial ℚ) : RootRing :=
  Polynomial.eval₂ (algebraMap ℚ RootRing) scalarS f

def scalarPolynomialHomogeneous (f : Polynomial ℚ) (n : ℕ) : Prop :=
  f.support ⊆ {n}

def vectorSpaceDirectSum
    (U V W : Submodule ℚ RootRing) : Prop :=
  U ⊔ V = W ∧ Disjoint U V

def claim_23448 : Prop :=
  (1 : RootRing) ∈ scalarRootedFactorAlgebra ∧
  rootStable scalarRootedFactorAlgebra ∧
  (∀ S : Subalgebra ℚ RootRing,
    rootStable S → scalarRootedFactorAlgebra ≤ S)

def claim_23449 : Prop :=
  toricSpecialization rootZ = toricV ∧
  (∀ k : ℕ,
    toricSpecialization (Polynomial.C (coefficientVariable k)) =
      toricU * toricV ^ (k + 1)) ∧
  (∀ k : ℕ, 1 ≤ k →
    toricSpecialization (rootX k) = toricU * toricV ^ k) ∧
  scalarW = toricSpecialization scalarS

def claim_23450 : Prop :=
  (∀ P : RootRing,
    toricSpecialization (rootClosure P) =
      scalarW * toricSpecialization P) ∧
  (1 : RootRing) ∈ scalarPreimage ∧
  (∀ P : RootRing, P ∈ scalarPreimage → rootClosure P ∈ scalarPreimage)

def claim_23451 : Prop :=
  scalarRootedFactorAlgebra = scalarPreimage ∧
  (∀ P : RootRing,
    P ∈ scalarRootedFactorAlgebra ↔
      ∃ Q : scalarImageSubalgebra,
        toricSpecialization P = scalarImageSubalgebra.val Q)

def claim_23452 : Prop :=
  coordinateSubalgebra = ⊤ ∧
  AlgebraicIndependent ℚ coordinateVariable ∧
  weightedHomogeneous rootZ 1 ∧
  weightedHomogeneous (rootX 1) 1 ∧
  (∀ k : triangularIndex,
    weightedHomogeneous (triangularDifference k.1) k.1)

def claim_23453 : Prop :=
  kernelIdeal =
    Ideal.span (Set.range (fun k : triangularIndex => triangularDifference k.1))

def eWeight (m : triangularIndex →₀ ℕ) : ℕ :=
  m.sum (fun k a => k.1 * a)

def eProduct (m : triangularIndex →₀ ℕ) : RootRing :=
  m.prod (fun k a => triangularDifference k.1 ^ a)

structure KernelMonomialIndex (n : ℕ) where
  zExponent : ℕ
  xExponent : ℕ
  eExponents : triangularIndex →₀ ℕ
  weight_eq : zExponent + xExponent + eWeight eExponents = n
  has_e_factor : eExponents.sum (fun _ a => a) > 0

def ScalarBasisIndex (n : ℕ) := Option (KernelMonomialIndex n)

def scalarBasisVector {n : ℕ} : ScalarBasisIndex n → RootRing
  | none => scalarS ^ n
  | some q =>
      rootZ ^ q.zExponent * rootX 1 ^ q.xExponent * eProduct q.eExponents

def weightPiece (n : ℕ) : Submodule ℚ RootRing :=
  Submodule.span ℚ {P : RootRing | weightedHomogeneous P n}

def scalarPiece (n : ℕ) : Submodule ℚ RootRing :=
  scalarRootedFactorAlgebra.toSubmodule ⊓ weightPiece n

def claim_23458 : Prop :=
  (∀ P : RootRing, P ∈ scalarRootedFactorAlgebra →
    ∃! q : Polynomial ℚ × RootRing,
      q.2 ∈ kernelIdeal ∧ P = evaluateAtScalar q.1 + q.2) ∧
  vectorSpaceDirectSum scalarSubalgebra.toSubmodule
    kernelSubmodule
    scalarRootedFactorAlgebra.toSubmodule ∧
  (∀ n : ℕ, ∀ P : RootRing,
    P ∈ scalarRootedFactorAlgebra → weightedHomogeneous P n →
      ∃! q : Polynomial ℚ × RootRing,
        q.2 ∈ kernelIdeal ∧
        scalarPolynomialHomogeneous q.1 n ∧
        weightedHomogeneous q.2 n ∧
        P = evaluateAtScalar q.1 + q.2)

def claim_23459 : Prop :=
  ∀ n : ℕ,
    LinearIndependent ℚ (scalarBasisVector (n := n)) ∧
    Submodule.span ℚ (Set.range (scalarBasisVector (n := n))) =
      scalarPiece n

def partitionNumber (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun m : Fin n → Fin (n + 1) =>
    (Finset.univ.sum (fun i => (i.1 + 1) * (m i).1)) = n)).card

abbrev QuotientCoordinateRing := MvPolynomial (Fin 2) ℚ

def quotientCoordinateWeightPiece (n : ℕ) :
    Submodule ℚ QuotientCoordinateRing :=
  Submodule.span ℚ {P : QuotientCoordinateRing |
    ∀ m ∈ P.support, m 0 + m 1 = n}

def quotientWeightSubmodule (n : ℕ) :
    Submodule ℚ (RootRing ⧸ kernelSubmodule) :=
  (weightPiece n).map (Submodule.mkQ kernelSubmodule)

def claim_23460 : Prop :=
  ∀ n : ℕ,
    Module.finrank ℚ (weightPiece n) =
      (Finset.range (n + 1)).sum partitionNumber ∧
    Nonempty ((quotientWeightSubmodule n) ≃ₗ[ℚ]
      quotientCoordinateWeightPiece n) ∧
    Module.finrank ℚ (quotientCoordinateWeightPiece n) = n + 1 ∧
    Module.finrank ℚ (scalarPiece n) =
      (Finset.range (n + 1)).sum partitionNumber - n

def hilbertSeriesA : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (Module.finrank ℚ (scalarPiece n) : ℚ))

def partitionGeneratingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (partitionNumber n : ℚ))

def claim_23461 : Prop :=
  hilbertSeriesA =
    partitionGeneratingSeries * (1 - PowerSeries.X)⁻¹ -
      PowerSeries.X * (1 - PowerSeries.X)⁻¹ ^ 2

def conductorIdeal : Ideal RootRing :=
  Ideal.span (Set.range (fun k : triangularIndex => triangularDifference k.1))

def scalarRing : Subring RootRing := scalarRootedFactorAlgebra.toSubring

abbrev ScalarRing := (scalarRing : Type)

def scalarRingKernelIdeal : Ideal ScalarRing :=
  Ideal.comap scalarRing.subtype conductorIdeal

def claim_23495 : Prop :=
  conductorIdeal = kernelIdeal ∧
  scalarRootedFactorAlgebra.toSubmodule =
    scalarSubalgebra.toSubmodule ⊔ conductorIdeal.restrictScalars ℚ ∧
  Disjoint scalarSubalgebra.toSubmodule (conductorIdeal.restrictScalars ℚ) ∧
  AlgebraicIndependent ℚ coordinateVariable ∧
  Nonempty ((ScalarRing ⧸ scalarRingKernelIdeal) ≃+* Polynomial ℚ) ∧
  Nonempty (((RootRing : Type) ⧸ conductorIdeal) ≃ₐ[ℚ]
    QuotientCoordinateRing)

end
end MathlibPlus.Open.ResearchFormalization
