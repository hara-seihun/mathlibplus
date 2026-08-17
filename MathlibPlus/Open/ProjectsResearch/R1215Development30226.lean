import MathlibPlus.Open.ProjectsResearch.R1215

namespace MathlibPlus.Open.ProjectsResearch.R1215Development30226

open MathlibPlus.Open.ProjectsResearch.R1215

/-- A point map and a block-index map identifying two translation
 developments.  No line map is included in this carrier. -/
def developmentIsomorphism
    (B C : Finset C7Squared)
    (f : C7Squared ≃ C7Squared)
    (σ : C7Squared ≃ C7Squared) : Prop :=
  ∀ d : C7Squared,
    Finset.image f (translate B d) = translate C (σ d)

/-- Claim 30226: an arbitrary point/block development isomorphism preserves
all block intersections and intrinsically recovers a target relative
difference-set line. -/
def claim_30226 : Prop :=
  ∀ (B C : Finset C7Squared) (H : AddSubgroup C7Squared)
    (f : C7Squared ≃ C7Squared) (σ : C7Squared ≃ C7Squared),
    RelativeDifferenceSet B H →
      developmentIsomorphism B C f σ →
        ∃ K : AddSubgroup C7Squared,
          Nat.card K = 7 ∧
            RelativeDifferenceSet C K ∧
              (∀ d e : C7Squared,
                (translate B d ∩ translate B e).card =
                  (translate C (σ d) ∩ translate C (σ e)).card)

end MathlibPlus.Open.ProjectsResearch.R1215Development30226
