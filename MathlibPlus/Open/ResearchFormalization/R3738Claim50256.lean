import MathlibPlus.Open.ResearchFormalization.R3738Claim50252
import MathlibPlus.Open.ResearchFormalization.BatchR3738Claim50257

namespace MathlibPlus.Open.ResearchFormalization.R3738Claim50256

open MathlibPlus.Open.Combinatorics.TreeBatch
open MathlibPlus.Open.ResearchFormalization.BatchR3738
open MathlibPlus.Open.ResearchFormalization.R3738Claim50252

noncomputable section

abbrev RootedForestProduct := RootedFactorPolynomial

def nonzeroGenuineProductSecant (R S : RTree) : Prop :=
  rootedTreePredicate R ∧ rootedTreePredicate S ∧ R.size = S.size ∧
    rootBranchProduct R - rootBranchProduct S ≠ 0

def commonSelectorKernel (E : RootedForestProduct) : Prop :=
  A₁ E = 0 ∧ A₂ E = 0

def barredE (t u r v s : ℚ) (E : RootedForestProduct) : ℚ :=
  baseSpecialization t u r v s E

def barredEZero (t u r v : ℚ) (E : RootedForestProduct) : ℚ :=
  baseConstantSpecialization t u r v E

def dottedEZero (t u r v : ℚ) (E : RootedForestProduct) : ℚ :=
  normalConstantSpecialization t u r v E

/-- Claim 50256: every nonzero genuine-product secant in the two-selector
kernel has a nonzero unspecialized deletion coefficient, a base-flat value at
r and at the constant marker, and the exact transverse normal coupling. -/
def nonzeroSecantBaseFlatNormal_claim50256 : Prop :=
  ∀ (t u r v : ℚ) (R S : RTree),
    nonzeroGenuineProductSecant R S →
      u ≠ 0 → r ≠ 0 → t - u ≠ 0 →
        let E : RootedForestProduct := rootBranchProduct R - rootBranchProduct S
        commonSelectorKernel E →
          E.coeff 0 ≠ 0 ∧
            barredE t u r v r E = 0 ∧
              barredEZero t u r v E = 0 ∧
                (v - r) * barredE t u r v v E =
                  r * (t - u) * dottedEZero t u r v E

end

end MathlibPlus.Open.ResearchFormalization.R3738Claim50256
