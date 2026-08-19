import MathlibPlus.Open.ResearchFormalization.R0765Claim26919

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.ResearchFormalization.R0770CavityMason

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0765Claim26919
open MathlibPlus.Open.RootedTreeBoundary

abbrev Coeff := MvPolynomial ℕ ℚ

/-- The lower-variable coefficient ring for a factor of order `m`, with the
source variables indexed as `x₁, ..., xₘ₋₁`. -/
def lowerVariableRing (m : ℕ) : Subalgebra ℚ Coeff :=
  Algebra.adjoin ℚ
    (Set.range (fun j : Fin (m - 1) => MvPolynomial.X (j.1 + 1)))

abbrev LowerCoeff (m : ℕ) := lowerVariableRing m
abbrev LowerField (m : ℕ) := FractionRing (LowerCoeff m)
abbrev RootedTree := RootedFiniteTree

/-- An actual root-deleted cavity polynomial together with the verified fact
that it lies in the lower-variable ring. -/
structure CavityValue (m : ℕ) where
  tree : RootedTree
  lowerOrder : Fintype.card tree.V < m
  lower : cavity tree ∈ LowerCoeff m

/-- The cavity value in the characteristic-zero fraction field of the lower
variable ring. -/
def cavityValue {m : ℕ} (A : CavityValue m) : LowerField m :=
  algebraMap (LowerCoeff m) (LowerField m) ⟨cavity A.tree, A.lower⟩

/-- The exact split characteristic core carrier: its three coefficients, the
three original split products, the residual split products, and their common
gcd factor. -/
structure CavityCharacteristicCore (m e d : ℕ) where
  coefficients : Fin 3 → ℚ
  originalRoots : Fin 3 → Fin e → CavityValue m
  residualRoots : Fin 3 → Fin d → CavityValue m
  commonGcd : Polynomial (LowerField m)

/-- The monic split polynomial of the original cavity values in one row. -/
def originalPolynomial {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) (i : Fin 3) :
    Polynomial (LowerField m) :=
  ∏ j : Fin e,
    (Polynomial.X - Polynomial.C (cavityValue (s.originalRoots i j)))

/-- The monic residual split polynomial in one row. -/
def residualPolynomial {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) (i : Fin 3) :
    Polynomial (LowerField m) :=
  ∏ j : Fin d,
    (Polynomial.X - Polynomial.C (cavityValue (s.residualRoots i j)))

/-- A scalar coefficient, viewed in the lower-variable fraction-field
polynomial ring. -/
def scalarPolynomial {m : ℕ} (a : ℚ) : Polynomial (LowerField m) :=
  Polynomial.C (algebraMap ℚ (LowerField m) a)

/-- The affine relation before common-gcd cancellation. -/
def originalAffineRelation {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) : Prop :=
  ∑ i : Fin 3,
      scalarPolynomial (s.coefficients i) * originalPolynomial s i = 0

/-- The affine relation after removing the common monic gcd. -/
def residualAffineRelation {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) : Prop :=
  ∑ i : Fin 3,
      scalarPolynomial (s.coefficients i) * residualPolynomial s i = 0

/-- Pairwise coprimality of the three residual polynomials. -/
def pairwiseCoprime3 {K : Type*} [Field K]
    (P : Fin 3 → Polynomial K) : Prop :=
  ∀ i j : Fin 3, i ≠ j → IsCoprime (P i) (P j)

/-- The common monic gcd condition used by the gcd-free split core. -/
def isCommonMonicGcd {K : Type*} [Field K]
    (H : Polynomial K) (P : Fin 3 → Polynomial K) : Prop :=
  H.Monic ∧
    (∀ i : Fin 3, H ∣ P i) ∧
      ∀ D : Polynomial K, D.Monic →
        (∀ i : Fin 3, D ∣ P i) → D ∣ H

/-- The complete characteristic-zero lower-variable and affine/gcd context of
Claims 24579 and 24582. -/
def cavityCharacteristicCoreValid {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) : Prop :=
  1 ≤ m ∧
    1 ≤ d ∧
    (∀ i : Fin 3, s.coefficients i ≠ 0) ∧
    (∑ i : Fin 3, s.coefficients i = 0) ∧
    (∀ i : Fin 3, (originalPolynomial s i).Monic) ∧
    (∀ i j : Fin 3,
      (originalPolynomial s i).natDegree = (originalPolynomial s j).natDegree) ∧
    (∀ i : Fin 3,
      (residualPolynomial s i).Monic ∧
        (residualPolynomial s i).natDegree = d) ∧
    isCommonMonicGcd s.commonGcd (originalPolynomial s) ∧
    (∀ i : Fin 3,
      originalPolynomial s i = s.commonGcd * residualPolynomial s i) ∧
    pairwiseCoprime3 (residualPolynomial s) ∧
    originalAffineRelation s ∧
    residualAffineRelation s

/-- The number of distinct actual cavity values in one residual row. -/
def cavityCount {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) (i : Fin 3) : ℕ :=
  Set.ncard (Set.range (fun j : Fin d =>
    cavityValue (s.residualRoots i j)))

/-- The total distinct-cavity diversity of a three-row residual core. -/
def cavityDiversity {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) : ℕ :=
  ∑ i : Fin 3, cavityCount s i

/-- The Wronskian formed from the first two coefficient-scaled residual rows. -/
def cavityWronskian {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) : Polynomial (LowerField m) :=
  let P₀ := scalarPolynomial (s.coefficients 0) * residualPolynomial s 0
  let P₁ := scalarPolynomial (s.coefficients 1) * residualPolynomial s 1
  P₀.derivative * P₁ - P₀ * P₁.derivative

/-- The lower-degree and upper-degree form of the Mason--Stothers conclusion. -/
def masonDiversityBound {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) : Prop :=
  ((3 * d : ℕ) : ℤ) - (cavityDiversity s : ℤ) ≤
      (cavityWronskian s).natDegree ∧
    (cavityWronskian s).natDegree ≤ ((2 * d - 1 : ℕ) : ℤ) ∧
    d + 1 ≤ cavityDiversity s

/-- The diversity inequality isolated for the pure-power contradiction. -/
def masonLowerDiversity {m e d : ℕ}
    (s : CavityCharacteristicCore m e d) : Prop :=
  d + 1 ≤ cavityDiversity s

/-- Pure-power residuals with three actual cavity values. -/
def purePowerResiduals {m e d : ℕ}
    (s : CavityCharacteristicCore m e d)
    (A : Fin 3 → CavityValue m) : Prop :=
  ∀ i : Fin 3,
    residualPolynomial s i =
      (Polynomial.X - Polynomial.C (cavityValue (A i))) ^ d

/-- Pairwise distinctness of the three cavity values in the pure-power branch. -/
def pairwiseDistinctCavities {m : ℕ}
    (A : Fin 3 → CavityValue m) : Prop :=
  ∀ i j : Fin 3, i ≠ j →
    cavityValue (A i) ≠ cavityValue (A j)

/-- Claim 24582: in the exact nonconstant lower-variable affine relation,
common-gcd cancellation and Wronskian divisibility force the displayed degree
bounds and the distinct-cavity diversity inequality. -/
def claim_24582 : Prop :=
  ∀ (m e d : ℕ) (s : CavityCharacteristicCore m e d),
    cavityCharacteristicCoreValid s → masonDiversityBound s

/-- Claim 24583: actual pure powers have exactly one distinct cavity value per
row, while the Mason conclusion from the same affine/gcd context would require
at least `d + 1`; degrees `d ≥ 3` are therefore impossible. -/
def claim_24583 : Prop :=
  ∀ (m e d : ℕ) (s : CavityCharacteristicCore m e d)
    (A : Fin 3 → CavityValue m),
    cavityCharacteristicCoreValid s →
      3 ≤ d →
        purePowerResiduals s A →
          pairwiseDistinctCavities A →
            cavityDiversity s = 3 ∧
              masonLowerDiversity s ∧
                ¬(3 ≥ d + 1)

end

end MathlibPlus.Open.ResearchFormalization.R0770CavityMason
