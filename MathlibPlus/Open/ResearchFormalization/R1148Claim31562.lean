import MathlibPlus.Open.ResearchFormalization.R1148Claim41326

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim31562

open MathlibPlus.Open.ResearchFormalization.R1148Claim41326

/-- Claim 31562: the exact translation-development census on `C₇`, with its
affine-image conclusion, normalized-label counts, and nonlinear signature
injectivity. -/
def claim31562 : Prop :=
  Fintype.card (Equiv.Perm C7) = 5040 ∧
    Set.ncard admissibleSubsets = 112 ∧
      Set.ncard developmentIsomorphismInstances = 12936 ∧
        (∀ (B : Set C7) (π : Equiv.Perm C7),
          (B, π) ∈ developmentIsomorphismInstances →
            ∃ (a : C7ˣ) (b : C7), affineImage a b B = pointImage π B) ∧
          Set.ncard normalizedLabels = 90 ∧
            Set.ncard scalarLabels = 6 ∧
              Set.ncard nonlinearLabels = 84 ∧
                ∀ δ ∈ nonlinearLabels,
                  Function.Injective (offsetSignature δ)

end MathlibPlus.Open.ResearchFormalization.R1148Claim31562
