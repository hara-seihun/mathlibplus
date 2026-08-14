import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
open Polynomial

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The equilibrium measure obtained by pushing normalized angular measure through `θ ↦ 2 cos θ`. -/
def traceEquilibriumMeasure : Measure ℝ :=
  Measure.map (fun θ : ℝ => 2 * Real.cos θ)
    (((ENNReal.ofReal ((2 * Real.pi)⁻¹)) : ℝ≥0∞) •
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))

/-- Reciprocal trace escape potential, with the maximum written as the supremum of the
moduli of the two roots of the displayed quadratic. -/
def reciprocalTraceEscape (u : ℝ) : ℝ :=
  Real.log (sSup {r : ℝ | ∃ z : ℂ,
    z ^ 2 - (u : ℂ) * z + 1 = 0 ∧ r = ‖z‖})

/-- The polynomial obtained from `x^d A(x+x⁻¹)` by expanding each power without
introducing Laurent-polynomial notation. -/
def reciprocalLift (A : Polynomial ℤ) : Polynomial ℂ :=
  Finset.sum (Finset.range (A.natDegree + 1)) (fun i =>
    Polynomial.C ((A.coeff i : ℤ) : ℂ) *
      Polynomial.X ^ (A.natDegree - i) *
      (Polynomial.X ^ 2 + 1) ^ i)

/-- Jensen--Mahler averaging for a nonzero integral polynomial. -/
def jensenMahlerAveragingIdentity : Prop :=
  ∀ A : Polynomial ℤ, A ≠ 0 →
    ((∫ u : ℝ, Real.log ‖Polynomial.eval u (A.map (Int.castRingHom ℝ))‖
        ∂traceEquilibriumMeasure) =
      (2 * Real.pi)⁻¹ *
        (∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
          Real.log ‖Polynomial.eval₂ (Int.castRingHom ℂ)
            (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I)) A‖)) ∧
      ((2 * Real.pi)⁻¹ *
        (∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
          Real.log ‖Polynomial.eval₂ (Int.castRingHom ℂ)
            (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I)) A‖) =
      Real.log (Polynomial.mahlerMeasure (reciprocalLift A)))

/-- The finite-family pointwise obstruction, with the exceptional set written as the
actual zero set of the auxiliary polynomials. -/
def nonpositiveGapAveragingTheorem : Prop :=
  ∀ (r : ℕ) (A : Fin r → Polynomial ℤ) (weights : Fin r → ℝ) (c : ℝ),
    (∀ j, A j ≠ 0) → (∀ j, 0 ≤ weights j) →
    (∀ u : ℝ, u ∈ Set.Icc (-2) 2 →
      (∀ j, Polynomial.eval u ((A j).map (Int.castRingHom ℝ)) ≠ 0) →
      reciprocalTraceEscape u ≥
        c + ∑ j, weights j * Real.log ‖Polynomial.eval u ((A j).map (Int.castRingHom ℝ))‖) →
    c ≤ 0

/-- The integrated certificate inequality associated with the same finite family. -/
def integratedCertificateInequality : Prop :=
  ∀ (r : ℕ) (A : Fin r → Polynomial ℤ) (weights : Fin r → ℝ) (c : ℝ),
    (∀ j, A j ≠ 0) → (∀ j, 0 ≤ weights j) →
    (∀ u : ℝ, u ∈ Set.Icc (-2) 2 →
      (∀ j, Polynomial.eval u ((A j).map (Int.castRingHom ℝ)) ≠ 0) →
      reciprocalTraceEscape u ≥
        c + ∑ j, weights j * Real.log ‖Polynomial.eval u ((A j).map (Int.castRingHom ℝ))‖) →
    0 ≥ c + ∑ j, weights j *
      Real.log (Polynomial.mahlerMeasure (reciprocalLift (A j))) ∧
      c + ∑ j, weights j *
        Real.log (Polynomial.mahlerMeasure (reciprocalLift (A j))) ≥ c

/-- A direct definition of finite-modulus root counts for a polynomial. -/
def complexRoots (P : Polynomial ℤ) : Multiset ℂ :=
  Polynomial.roots (P.map (Int.castRingHom ℂ))

def rootCountOutside (P : Polynomial ℤ) : ℕ :=
  (complexRoots P).countP (fun z => ‖z‖ > 1)

def rootCountOnUnitCircle (P : Polynomial ℤ) : ℕ :=
  (complexRoots P).countP (fun z => ‖z‖ = 1)

/-- The explicitly displayed reciprocal degree-six witness and its root ledger. -/
def reciprocalSourcePolynomial : Polynomial ℤ :=
  Polynomial.X ^ 6 + 2 * Polynomial.X ^ 4 + Polynomial.X ^ 3 +
    2 * Polynomial.X ^ 2 + 1

def exactReciprocalSourcePolynomial : Prop :=
  let P := reciprocalSourcePolynomial
  P.natDegree = 6 ∧
  P.Monic ∧
  P.reverse = P ∧
  Irreducible (P.map (Int.castRingHom ℚ)) ∧
  (∀ n : ℕ, P ≠ Polynomial.cyclotomic n ℤ) ∧
  rootCountOutside P = 2 ∧
  rootCountOnUnitCircle P = 2 ∧
  (∀ z : ℂ, z ∈ complexRoots P → z⁻¹ ∈ complexRoots P)

/-- A natural-number multiplicative order, expressed as the least positive exponent
whose residue is one. -/
def natModOrder (a n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ n ∣ a ^ k - 1}

/-- Multiplicative-order lifting at the prime `3`. -/
def multiplicativeOrderLiftingAtThree : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≠ 3 →
    let f := natModOrder p 3
    let c := padicValNat 3 (p ^ f - 1)
    ∀ k : ℕ, k > c → natModOrder p (3 ^ k) = f * 3 ^ (k - c)

/-- The cyclotomic family `Φ_(3^k)` is irreducible modulo two, with the exact
order computation used in the claim. -/
def cyclotomicFamilyModTwo : Prop :=
  (natModOrder 2 3 = 2) ∧
  (padicValNat 3 (2 ^ natModOrder 2 3 - 1) = 1) ∧
  (∀ k : ℕ, 1 ≤ k →
    natModOrder 2 (3 ^ k) = 2 * 3 ^ (k - 1) ∧
    Irreducible (Polynomial.cyclotomic (3 ^ k) (ZMod 2)))

/-- An algebraic unit is represented by integral equations for both the element and
its inverse; this is the semantic content needed for the cyclotomic-root claim. -/
def algebraicUnit (z : AlgebraicClosure ℚ) : Prop :=
  z ≠ 0 ∧
  (∃ q : Polynomial ℤ, q.Monic ∧
    Polynomial.eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) z q = 0) ∧
  (∃ q : Polynomial ℤ, q.Monic ∧
    Polynomial.eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) z⁻¹ q = 0)

/-- Monicity, rational irreducibility, constant coefficient one, reciprocity, and
unit inverse-pairing for the family `Φ_(3^k)`, `k ≥ 1`. -/
def cyclotomicReciprocalUnitFamily : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let p := Polynomial.cyclotomic (3 ^ k) ℤ
    p.Monic ∧
    Irreducible (p.map (Int.castRingHom ℚ)) ∧
    p.coeff 0 = 1 ∧
    p.reverse = p ∧
    (∀ z : AlgebraicClosure ℚ,
      Polynomial.IsRoot (p.map (Int.castRingHom (AlgebraicClosure ℚ))) z →
      algebraicUnit z ∧
      Polynomial.IsRoot (p.map (Int.castRingHom (AlgebraicClosure ℚ))) z⁻¹)

/-- The explicitly displayed reciprocal degree-eighteen witness. -/
def reciprocalDegreeEighteenPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 18 - Polynomial.X ^ 17 + Polynomial.X ^ 16 - Polynomial.X ^ 15 -
    Polynomial.X ^ 12 + Polynomial.X ^ 11 - Polynomial.X ^ 10 + Polynomial.X ^ 9 -
    Polynomial.X ^ 8 + Polynomial.X ^ 7 - Polynomial.X ^ 6 - Polynomial.X ^ 3 +
    Polynomial.X ^ 2 - Polynomial.X + 1

def reciprocalDegreeEighteenWitness : Prop :=
  let p := reciprocalDegreeEighteenPolynomial
  p.natDegree = 18 ∧
  p.Monic ∧
  p.reverse = p ∧
  Irreducible (p.map (Int.castRingHom ℚ)) ∧
  (∀ n : ℕ, p ≠ Polynomial.cyclotomic n ℤ) ∧
  rootCountOutside p = 1 ∧
  rootCountOnUnitCircle p = 16 ∧
  (∀ z : ℂ, z ∈ complexRoots p → z⁻¹ ∈ complexRoots p)

/-- The qualitative Salem-root ledger for the displayed degree-eighteen polynomial,
including the stated numerical localization. -/
def smallSalemExteriorRoot : Prop :=
  let p := reciprocalDegreeEighteenPolynomial
  p.natDegree = 18 ∧
  p.Monic ∧
  p.reverse = p ∧
  Irreducible (p.map (Int.castRingHom ℚ)) ∧
  rootCountOutside p = 1 ∧
  rootCountOnUnitCircle p = 16 ∧
  ∃ σ : ℝ,
    (1.188368 : ℝ) < σ ∧ σ < (1.188369 : ℝ) ∧
    1 < σ ∧
    Polynomial.IsRoot (p.map (Int.castRingHom ℝ)) σ ∧
    Polynomial.IsRoot (p.map (Int.castRingHom ℝ)) σ⁻¹ ∧
    (∀ z : ℂ, z ∈ complexRoots p →
      z = σ ∨ z = σ⁻¹ ∨ ‖z‖ = 1)

/-- The roots of the minimal polynomial of a real algebraic number, viewed in `ℂ`. -/
def algebraicNumberRoots (β : ℝ) : Multiset ℂ :=
  Polynomial.roots ((minpoly ℚ β).map (algebraMap ℚ ℂ))

def rootCountWithModulus (β : ℝ) (r : ℝ) : ℕ :=
  (algebraicNumberRoots β).countP (fun z => ‖z‖ = r)

def algebraicMahlerMeasure (β : ℝ) : ℝ :=
  Polynomial.mahlerMeasure ((minpoly ℚ β).map (algebraMap ℚ ℂ))

def realAlgebraicUnit (β : ℝ) : Prop :=
  IsIntegral ℤ β ∧ IsIntegral ℤ β⁻¹

def PerronNumber (β : ℝ) : Prop :=
  1 < β ∧ ∀ z : ℂ, z ∈ algebraicNumberRoots β →
    z ≠ (β : ℂ) → ‖z‖ < β

def PisotLike (β : ℝ) : Prop :=
  1 < β ∧ IsIntegral ℤ β ∧ ∀ z : ℂ, z ∈ algebraicNumberRoots β →
    z ≠ (β : ℂ) → ‖z‖ < 1

def SalemLike (β : ℝ) : Prop :=
  1 < β ∧ realAlgebraicUnit β ∧
    (∀ z : ℂ, z ∈ algebraicNumberRoots β →
      z ≠ (β : ℂ) → ‖z‖ ≤ 1) ∧
    ∃ z : ℂ, z ∈ algebraicNumberRoots β ∧ z ≠ (β : ℂ) ∧ ‖z‖ = 1

/-- The exact exterior-root product and the twelve-conjugate modulus ledger. -/
def exteriorProductData (β a : ℝ) (z₁ z₂ : ℂ) : Prop :=
  let P := reciprocalSourcePolynomial
  rootCountOutside P = 2 ∧
  1 < β ∧ 1 < a ∧ β = a ^ 2 ∧
  Polynomial.IsRoot (P.map (Int.castRingHom ℂ)) z₁ ∧
  Polynomial.IsRoot (P.map (Int.castRingHom ℂ)) z₂ ∧
  ‖z₁‖ > 1 ∧ ‖z₂‖ > 1 ∧ z₁ ≠ z₂ ∧
  (β : ℂ) = z₁ * z₂ ∧
  β = Polynomial.mahlerMeasure (P.map (Int.castRingHom ℂ)) ∧
  Irreducible (minpoly ℚ β) ∧ (minpoly ℚ β).natDegree = 12 ∧
  rootCountWithModulus β (a ^ 2) = 1 ∧
  rootCountWithModulus β a = 4 ∧
  rootCountWithModulus β 1 = 2 ∧
  rootCountWithModulus β a⁻¹ = 4 ∧
  rootCountWithModulus β (a⁻¹ ^ 2) = 1

def exteriorRootProductAndConjugateLedger : Prop :=
  ∃ β a : ℝ, ∃ z₁ z₂ : ℂ, exteriorProductData β a z₁ z₂

/-- The unique-house Perron unit and the failure of the Pisot and Salem conditions. -/
def uniqueHousePerronUnit : Prop :=
  ∃ β a : ℝ, ∃ z₁ z₂ : ℂ,
    exteriorProductData β a z₁ z₂ ∧
    realAlgebraicUnit β ∧ PerronNumber β ∧
    rootCountWithModulus β a = 4 ∧ ¬ PisotLike β ∧ ¬ SalemLike β

/-- Positive powers generate the same number field. -/
def powersGenerateSameNumberField : Prop :=
  ∃ β a : ℝ, ∃ z₁ z₂ : ℂ,
    exteriorProductData β a z₁ z₂ ∧
    (∀ m : ℕ, 1 ≤ m →
      Algebra.adjoin ℚ ({β ^ m} : Set ℝ) = Algebra.adjoin ℚ ({β} : Set ℝ))

/-- Positive powers preserve the algebraic degree. -/
def positivePowersPreserveDegree : Prop :=
  ∃ β a : ℝ, ∃ z₁ z₂ : ℂ,
    exteriorProductData β a z₁ z₂ ∧
    (∀ m : ℕ, 1 ≤ m →
      (minpoly ℚ (β ^ m)).natDegree = (minpoly ℚ β).natDegree ∧
      (minpoly ℚ (β ^ m)).natDegree = 12)

/-- Mahler measure of every positive power. -/
def mahlerMeasureOfPositivePowers : Prop :=
  ∃ β a : ℝ, ∃ z₁ z₂ : ℂ,
    exteriorProductData β a z₁ z₂ ∧
    (∀ m : ℕ, 1 ≤ m →
      algebraicMahlerMeasure (β ^ m) = algebraicMahlerMeasure β ^ m ∧
      algebraicMahlerMeasure β ^ m = β ^ (3 * m))

end MathlibPlus.Open.ResearchFormalizationBatch
