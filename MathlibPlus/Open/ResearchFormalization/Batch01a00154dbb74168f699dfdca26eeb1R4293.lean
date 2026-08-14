import MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1R4293

abbrev R4293BooleanAssignment :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.R4293BooleanAssignment

abbrev R4293BooleanFunction :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.R4293BooleanFunction

abbrev R4293DecisionTree :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.R4293DecisionTree

abbrev R4293Determines {n : ℕ} :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293Determines (n := n)

noncomputable abbrev R4293LawExpectation {n : ℕ} :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293LawExpectation (n := n)

noncomputable abbrev R4293PartialDerivative {n : ℕ} :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293PartialDerivative (n := n)

noncomputable abbrev R4293PivotalMass {n : ℕ} :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293PivotalMass (n := n)

noncomputable abbrev R4293TreeQueryMass {n : ℕ} :=
  MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support.r4293TreeQueryMass (n := n)

/-- Pointwise pivotal-mass inequality for a finite law of Boolean functions. -/
def r4293PointwisePivotalMassInequality (n : ℕ)
    (lambda : PMF (R4293BooleanFunction n))
    (trees : R4293BooleanFunction n → R4293DecisionTree n) : Prop :=
  (∀ H, R4293Determines (trees H) H) →
    ∀ (x : R4293BooleanAssignment n) (i : Fin n),
      |R4293PartialDerivative (R4293LawExpectation lambda) x i| ≤
          R4293PivotalMass lambda x i ∧
        R4293PivotalMass lambda x i ≤ R4293TreeQueryMass lambda trees x i

end MathlibPlus.Open.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1R4293
