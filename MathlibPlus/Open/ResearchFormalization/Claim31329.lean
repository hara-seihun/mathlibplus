import MathlibPlus.Open.ResearchFormalization.Claim31331

namespace MathlibPlus.Open.ResearchFormalization.Claim31329

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Claim31331

/-- The linear factor `z + λv` in the outer `z` polynomial variable. -/
def linearBoundaryFactor_claim31329 (lambda : ℚ) : ShiftedBoundaryPolynomial :=
  rootZVariable + Polynomial.C (Polynomial.C lambda) * rootVVariable

/--
Claim 31329: for root degree at least two, a divisor `z + λv` of the
shifted boundary atom forces `λ = 1` and the exact leaf-child condition.
-/
def rootDegreeAtLeastTwoLinearFactorClaim_claim31329 : Prop :=
  ∀ R : RootedTreeBoundary.RootedFiniteTree,
    2 ≤ rootedTreeDegree R R.root →
    ∀ lambda : ℚ,
      linearBoundaryFactor_claim31329 lambda ∣ shiftedBoundaryD R →
        lambda = 1 ∧ hasRootLeafChild R

end

end MathlibPlus.Open.ResearchFormalization.Claim31329
