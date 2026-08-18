import MathlibPlus.Open.ResearchFormalization.Claim17072

namespace MathlibPlus.Open.ResearchFormalization

open MathlibPlus.Open.FormalizationBatch

/-- Claim 17068: the displayed order-eight family is an involutive
fixed-index cocycle with the paired alternating-square component regime, and
all eight prescribed maps are global pairings. -/
def claim17068_allPrescribedWitnessMapsGlue : Prop :=
  ∃ π : PointedLocalPermutations V8,
    involutiveFixedIndexCocycle π ∧
      tableFamily π ∧
        exactAlternatingSquareRegime π ∧
          ∀ j : V8, globalPairing π (π.1 j)

end MathlibPlus.Open.ResearchFormalization
