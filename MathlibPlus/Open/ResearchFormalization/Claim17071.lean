import Mathlib
import MathlibPlus.Open.ResearchFormalization.Claim17072

namespace MathlibPlus.Open.ResearchFormalization.Claim17071

open MathlibPlus.Open.FormalizationBatch
open MathlibPlus.Open.Algebra.FormalizationBatch
open MathlibPlus.Open.ResearchFormalization

/-- Claim 17071: for the exact order-eight witness, the 48-element set of
    global pairings is a proper subset of all 8! permutations and contains
    every prescribed map. -/
def claim17071_exactly_48_global_pairings : Prop :=
  ∃ π : PointedLocalPermutations V8,
    involutiveFixedIndexCocycle π ∧
      tableFamily π ∧
        exactAlternatingSquareRegime π ∧
          Fintype.card (Equiv.Perm V8) = 40320 ∧
            (∃ S : Finset (Equiv.Perm V8),
              S.card = 48 ∧
                (∀ σ : Equiv.Perm V8, σ ∈ S ↔ globalPairing π σ)) ∧
              (∀ j : V8, globalPairing π (π.1 j)) ∧
                ¬ globalPairing π (Equiv.refl V8)

end MathlibPlus.Open.ResearchFormalization.Claim17071
