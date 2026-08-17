import Mathlib

open scoped BigOperators
open MvPolynomial

namespace MathlibPlus.Open.ResearchFormalization.R0854Claim25340

noncomputable section

abbrev ArmPolynomial := MvPolynomial (Fin 5) ℚ
abbrev SupportSet := Finset (Fin 5)

def supportedOn (S : SupportSet) (P : ArmPolynomial) : Prop :=
  ∀ d ∈ P.support, ∀ i, i ∉ S → d i = 0

def armSetZero (i : Fin 5) (P : ArmPolynomial) : ArmPolynomial :=
  MvPolynomial.eval₂ (algebraMap ℚ ArmPolynomial)
    (fun j => if j = i then 0 else MvPolynomial.X j) P

def facetBoundary (F : SupportSet → ArmPolynomial)
    (R : SupportSet) : ArmPolynomial := by
  classical
  exact Finset.sum (Finset.univ.filter (fun i : Fin 5 => i ∉ R))
    (fun i => armSetZero i (F (insert i R)))

def partialDerivative (i : Fin 5) (P : ArmPolynomial) : ArmPolynomial :=
  Finset.sum P.support (fun d =>
    MvPolynomial.monomial (d - Finsupp.single i 1)
      ((d i : ℚ) * P.coeff d))

def derivativeSum (P : ArmPolynomial) : ArmPolynomial :=
  Finset.sum Finset.univ (fun i : Fin 5 => partialDerivative i P)

def exactSupportFiveComponent (F : SupportSet → ArmPolynomial) : Prop :=
  (∀ S : SupportSet, supportedOn S (F S)) ∧
  (∀ S : SupportSet, S ≠ (Finset.univ : SupportSet) → F S = 0)

def translationInvariantSupportFivePage
    (F : SupportSet → ArmPolynomial) : Prop :=
  exactSupportFiveComponent F ∧
  derivativeSum (F Finset.univ) = 0

/-- Claim 25340: after imposing the exact-support bulk equation and the
four zero facet-residue equations, the support-five component vanishes.  The
bulk equation is the sum of the five partial derivatives, not five separate
vanishing equations; the divisibility conclusion is retained explicitly. -/
def exactSupportFiveVanishing_claim25340 : Prop :=
  ∀ F : SupportSet → ArmPolynomial,
    exactSupportFiveComponent F →
    derivativeSum (F Finset.univ) = 0 →
    (∀ R : SupportSet, R.card = 4 → facetBoundary F R = 0) →
      (∀ i : Fin 5, MvPolynomial.X i ∣ F Finset.univ) ∧
        F Finset.univ = 0

end

end MathlibPlus.Open.ResearchFormalization.R0854Claim25340
