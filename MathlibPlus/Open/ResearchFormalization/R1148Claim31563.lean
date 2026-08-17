import MathlibPlus.Open.ResearchFormalization.R1148Claim41327

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim31563

open MathlibPlus.Open.ResearchFormalization.R1148Claim41327

/-- Claim 31563: the exact nonaffine support, cyclic-Fano system, source and
target class, and nonlinear-label incidence census. -/
def claim31563 : Prop :=
  Fintype.card (Equiv.Perm C7) = 5040 ∧
    Set.ncard fanoA = 7 ∧ Set.ncard fanoB = 7 ∧ fanoA ≠ fanoB ∧
      (∀ F : Set (Set C7), F = fanoA ∨ F = fanoB →
        Set.ncard F = 7 ∧ ∀ L ∈ F, L.ncard = 3) ∧
        (∀ F : Set (Set C7), F = fanoA ∨ F = fanoB →
          Set.ncard (lineComplementFamily F) = 7 ∧
            ∀ C ∈ lineComplementFamily F, C.ncard = 4) ∧
          Set.ncard nonaffinePointPermutations = 588 ∧
            Set.ncard normalizedLabels = 90 ∧
              Set.ncard nonlinearLabels = 84 ∧
                (∀ π ∈ nonaffinePointPermutations,
                  Set.ncard (supportedSubsets π) = 14 ∧
                    Set.ncard (supportedTriples π) = 7 ∧
                      (∃ F G : Set (Set C7),
                        (F = fanoA ∨ F = fanoB) ∧
                          (G = fanoA ∨ G = fanoB) ∧
                            supportedTriples π = F ∧
                              imageLineSystem π F = G ∧
                                supportedSubsets π =
                                  F ∪ lineComplementFamily F) ∧
                      (∀ B ∈ supportedSubsets π,
                        ∀ δ : Equiv.Perm C7,
                          normalizedDevelopmentLabel B π δ →
                            ¬ scalarLabel δ) ∧
                      Set.ncard (pointLabels π) = 7 ∧
                        ∀ δ ∈ pointLabels π, δ ∈ nonlinearLabels) ∧
              Set.ncard (sourceSystemClass fanoA) = 294 ∧
                Set.ncard (sourceSystemClass fanoB) = 294 ∧
                  (∀ F G : Set (Set C7),
                    (F = fanoA ∨ F = fanoB) →
                      (G = fanoA ∨ G = fanoB) →
                        Set.ncard (orderedSystemClass F G) = 147) ∧
                    Set.ncard nonaffineLabelIncidences = 4116 ∧
                      ∀ δ ∈ nonlinearLabels,
                        Set.ncard
                            {π | (π, δ) ∈ nonaffineLabelIncidences} = 49

end MathlibPlus.Open.ResearchFormalization.R1148Claim31563
