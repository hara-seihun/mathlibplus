import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0854Claim25338

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ArmPolynomial25338 := MvPolynomial (Fin 5) ℚ
abbrev SupportSet25338 := Finset (Fin 5)

/-- The five-arm polynomial carrier used by the exact-support decomposition. -/
def supportedOn25338 (S : SupportSet25338) (P : ArmPolynomial25338) : Prop :=
  ∀ d ∈ P.support, ∀ i, i ∉ S → d i = 0

def armSetZero25338 (i : Fin 5) (P : ArmPolynomial25338) :
    ArmPolynomial25338 :=
  MvPolynomial.eval₂ (algebraMap ℚ ArmPolynomial25338)
    (fun j => if j = i then 0 else MvPolynomial.X j) P

def facetBoundary25338 (F : SupportSet25338 → ArmPolynomial25338)
    (R : SupportSet25338) : ArmPolynomial25338 :=
  ∑ i ∈ (Finset.univ.filter (fun i : Fin 5 => i ∉ R)),
    armSetZero25338 i (F (insert i R))

def partialDerivative25338 (i : Fin 5) (P : ArmPolynomial25338) :
    ArmPolynomial25338 :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial (d - Finsupp.single i 1)
      ((d i : ℚ) * P.coeff d)

def derivativeSum25338 (P : ArmPolynomial25338) : ArmPolynomial25338 :=
  ∑ i : Fin 5, partialDerivative25338 i P

def exactSupportFourComponent25338
    (F : SupportSet25338 → ArmPolynomial25338) : Prop :=
  (∀ S : SupportSet25338, S.card = 4 → supportedOn25338 S (F S)) ∧
    (∀ S : SupportSet25338, S.card ≠ 4 → F S = 0)

def supportFourKernelSet25338 (n : ℕ) :
    Set (SupportSet25338 → ArmPolynomial25338) :=
  {F |
    exactSupportFourComponent25338 F ∧
      (∀ S : SupportSet25338, S.card = 4 →
        F S ∈ MvPolynomial.homogeneousSubmodule (Fin 5) ℚ n) ∧
      (∀ S : SupportSet25338, S.card = 4 → derivativeSum25338 (F S) = 0) ∧
      (∀ R : SupportSet25338, R.card = 3 → facetBoundary25338 F R = 0)}

/-- The actual exact-support-four kernel in each homogeneous degree, formed
from the five-arm bulk and facet equations rather than from a free model. -/
def supportFourKernel25338 (n : ℕ) :
    Submodule ℚ (SupportSet25338 → ArmPolynomial25338) :=
  Submodule.span ℚ (supportFourKernelSet25338 n)

def supportFourHilbertCoefficient25338 (n : ℕ) : ℕ :=
  Module.finrank ℚ (supportFourKernel25338 n)

def supportFourHilbertSeries25338 : PowerSeries ℚ :=
  (PowerSeries.X : PowerSeries ℚ) ^ 6 *
      (1 - (PowerSeries.X : PowerSeries ℚ) ^ 2)⁻¹ *
    (1 - (PowerSeries.X : PowerSeries ℚ) ^ 3)⁻¹ *
    (1 - (PowerSeries.X : PowerSeries ℚ) ^ 4)⁻¹

/-- Claim 25338: the exact support-four kernel has the displayed all-degree
Hilbert series. -/
def claim25338 : Prop :=
  ∀ n : ℕ,
    PowerSeries.coeff n supportFourHilbertSeries25338 =
      (supportFourHilbertCoefficient25338 n : ℚ)

end

end MathlibPlus.Open.ResearchFormalization.R0854Claim25338
