import MathlibPlus.Open.ResearchFormalization.ScalarBatch01

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0044.Claim29304

noncomputable section

abbrev ScalarRootedRing :=
  MathlibPlus.Open.ResearchFormalization.RootedRing
def coefficientMonomialWeight (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun i a => (i + 1) * a)

def weightedHomogeneous (P : ScalarRootedRing) (n : ℕ) : Prop :=
  ∀ a ∈ P.support, ∀ m ∈ (P.coeff a).support,
    a + coefficientMonomialWeight m = n

def closedOnlyScalar (P : ScalarRootedRing) : Prop :=
  P ∈ MathlibPlus.Open.ResearchFormalization.rootedFactorAlgebra ∧
    MathlibPlus.Open.ResearchFormalization.zFree P

def closedHomogeneousPart (n : ℕ) : Submodule ℚ ScalarRootedRing :=
  Submodule.span ℚ
    {P : ScalarRootedRing |
      closedOnlyScalar P ∧ weightedHomogeneous P n}

def partitionNumber (n : ℕ) : ℕ :=
  Nat.card (Nat.Partition n)

def firstClosedOnlySurvivor : ScalarRootedRing :=
  Polynomial.C
    (MathlibPlus.Open.ResearchFormalization.xCoeff 0 *
      MathlibPlus.Open.ResearchFormalization.xCoeff 2 -
        MathlibPlus.Open.ResearchFormalization.xCoeff 1 ^ 2)

def firstClosedOnlyOperatedExpression : ScalarRootedRing :=
  2 * MathlibPlus.Open.ResearchFormalization.scalarS *
      MathlibPlus.Open.ResearchFormalization.scalarP -
    MathlibPlus.Open.ResearchFormalization.scalarS *
      MathlibPlus.Open.ResearchFormalization.scalarC -
    MathlibPlus.Open.ResearchFormalization.scalarE ^ 2 -
    MathlibPlus.Open.ResearchFormalization.rootedOperator
      MathlibPlus.Open.ResearchFormalization.scalarC +
    MathlibPlus.Open.ResearchFormalization.rootedOperator
      (MathlibPlus.Open.ResearchFormalization.scalarS ^ 3)

def noPositiveClosedOnlyBelowFour : Prop :=
  ∀ n : ℕ, 0 < n → n < 4 →
    ∀ P : ScalarRootedRing,
      closedOnlyScalar P → weightedHomogeneous P n → P = 0

def claim29304_firstClosedOnlySurvivorAndFiniteDimensions : Prop :=
  firstClosedOnlySurvivor ≠ 0 ∧
    closedOnlyScalar firstClosedOnlySurvivor ∧
    weightedHomogeneous firstClosedOnlySurvivor 4 ∧
    noPositiveClosedOnlyBelowFour ∧
    firstClosedOnlyOperatedExpression = firstClosedOnlySurvivor ∧
    Module.finrank ℚ (closedHomogeneousPart 1) = 0 ∧
    Module.finrank ℚ (closedHomogeneousPart 2) = 0 ∧
    Module.finrank ℚ (closedHomogeneousPart 3) = 0 ∧
    Module.finrank ℚ (closedHomogeneousPart 4) = 1 ∧
    Module.finrank ℚ (closedHomogeneousPart 5) = 2 ∧
    Module.finrank ℚ (closedHomogeneousPart 6) = 5 ∧
    Module.finrank ℚ (closedHomogeneousPart 7) = 8 ∧
    Module.finrank ℚ (closedHomogeneousPart 8) = 14 ∧
    (∀ n : ℕ, 4 ≤ n → n ≤ 8 →
      Module.finrank ℚ (closedHomogeneousPart n) =
        partitionNumber n - n)

end

end MathlibPlus.Open.ResearchFormalization.BatchQ0044.Claim29304
