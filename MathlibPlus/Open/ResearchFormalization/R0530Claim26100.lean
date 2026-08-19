import MathlibPlus.Open.ResearchFormalization.R0530Claim26120

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26100

open MathlibPlus.Open.ResearchFormalization.BatchR0532
open MathlibPlus.Open.ResearchFormalization.R0530Claim26120
open Polynomial

noncomputable section

/-- All coefficients strictly below the displayed grade are zero. -/
def coefficientsVanishBelow (P : Polynomial ℤ) (grade : ℕ) : Prop :=
  ∀ k : ℕ, k < grade → P.coeff k = 0

/-- The one-center summand attached to the `A` side in the reversed jet. -/
def oneCenterTermA
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  (∑ k ∈ Finset.range c, (Polynomial.X : Polynomial ℤ) ^ k) *
    ((Polynomial.X : Polynomial ℤ) ^ (B.sum + 1) *
      boundaryMarkedProduct A)

/-- The one-center summand attached to the `B` side in the reversed jet. -/
def oneCenterTermB
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  (∑ k ∈ Finset.range c, (Polynomial.X : Polynomial ℤ) ^ k) *
    ((Polynomial.X : Polynomial ℤ) ^ (A.sum + 1) *
      boundaryMarkedProduct B)

/-- For the admissible double-spider parameterization, the interval sector and
both oriented one-center sectors are absent through the stated grades of the
reversed excess-boundary series. -/
def boundarySupportSeparation_claim26100 : Prop :=
  ∀ T : DoubleSpider,
    admissibleDoubleSpider T →
      let m := min T.left.sum T.right.sum
      coefficientsVanishBelow
          (boundaryInternalExcess T.left T.right T.trunk) (m + 3) ∧
        coefficientsVanishBelow
          (oneCenterTermA T.left T.right T.trunk) (m + 2) ∧
        coefficientsVanishBelow
          (oneCenterTermB T.left T.right T.trunk) (m + 2)

end

end MathlibPlus.Open.ResearchFormalization.R0530Claim26100
