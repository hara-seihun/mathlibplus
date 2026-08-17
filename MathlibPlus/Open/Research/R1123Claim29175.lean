import MathlibPlus.Open.Research.R1123

namespace MathlibPlus.Open.Research

/-- The CI conclusion for one inverse-closed valency-twelve connection set. -/
def ciAt29175 (S : connectionSet censusGroup) : Prop :=
  ∀ T : connectionSet censusGroup,
    (∃ e : censusGroup ≃ censusGroup, ∀ x y : censusGroup,
      (y - x ∈ S.1 ↔ e y - e x ∈ T.1)) →
      ∃ e : censusGroup ≃+ censusGroup,
        ∀ x : censusGroup, x ∈ S.1 ↔ e x ∈ T.1

/-- Equality of the two exact quotient censuses forces the ordinary undirected
CI property at valency twelve. -/
def claim_29175 : Prop :=
  claim29174 → ∀ S : connectionSet censusGroup, ciAt29175 S

end MathlibPlus.Open.Research
