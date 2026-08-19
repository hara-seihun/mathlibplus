import MathlibPlus.Open.ResearchFormalization.R3738Claim50252
import MathlibPlus.Open.ResearchFormalization.BatchR3738Claim50257

namespace MathlibPlus.Open.ResearchFormalization.R3738Claim50250

open MathlibPlus.Open.Combinatorics.TreeBatch
open MathlibPlus.Open.ResearchFormalization.BatchR3738
open MathlibPlus.Open.ResearchFormalization.R3738Claim50252

noncomputable section

abbrev RootedForestProduct := RootedFactorPolynomial

def equalWeightGenuineSecant (R S : RTree) : Prop :=
  rootedTreePredicate R ∧ rootedTreePredicate S ∧ R.size = S.size

noncomputable def dualSelectorValue (t u r v : ℚ) (j : ℕ)
    (E : RootedForestProduct) : DualNumber ℚ :=
  dualCoefficientSpecialization t u r v (shiftedRootForgetting j E)

def barredSelectorValue (t u r v : ℚ) (j : ℕ)
    (E : RootedForestProduct) : ℚ :=
  (dualSelectorValue t u r v j E).1

def dottedSelectorValue (t u r v : ℚ) (j : ℕ)
    (E : RootedForestProduct) : ℚ :=
  (dualSelectorValue t u r v j E).2

/-- The barred and dotted root-marker evaluations of a genuine secant. -/
def barredE (t u r v s : ℚ) (E : RootedForestProduct) : ℚ :=
  baseSpecialization t u r v s E

def dottedE (t u r v s : ℚ) (E : RootedForestProduct) : ℚ :=
  normalSpecialization t u r v s E

def barredEZero (t u r v : ℚ) (E : RootedForestProduct) : ℚ :=
  baseConstantSpecialization t u r v E

def dottedEZero (t u r v : ℚ) (E : RootedForestProduct) : ℚ :=
  normalConstantSpecialization t u r v E

/-- Claim 50250: after the stated dual-number specialization, both shifted
root-forgetting selectors have their barred and dotted values displayed in
terms of the one-exponential and constant-marker evaluations. -/
def dualSelectorIdentities_claim50250 : Prop :=
  ∀ (t u r v : ℚ) (R S : RTree),
    equalWeightGenuineSecant R S →
      let E : RootedForestProduct := rootBranchProduct R - rootBranchProduct S
      barredSelectorValue t u r v 1 E =
          u * barredE t u r v r E + (t - u) * barredEZero t u r v E ∧
        barredSelectorValue t u r v 2 E =
          u * r * barredE t u r v r E ∧
        dottedSelectorValue t u r v 1 E =
          barredE t u r v v E - barredEZero t u r v E +
            u * dottedE t u r v r E + (t - u) * dottedEZero t u r v E ∧
        dottedSelectorValue t u r v 2 E =
          v * barredE t u r v v E + u * r * dottedE t u r v r E

end

end MathlibPlus.Open.ResearchFormalization.R3738Claim50250
