import MathlibPlus.Open.ResearchFormalizationD0079

namespace MathlibPlus.Open.ResearchFormalizationD0079

/-- A nonzero profile-eigenspace vector killed by the leaf-deck map is a
profile-local primitive and lies in the motif-observability defect. -/
def claim5083 : Prop :=
  ∀ (q n : ℕ)
    (profileValue : RetainedMotif q → ℕ)
    (w : V n),
    w ≠ 0 →
    w ∈ profileEigenspace q n profileValue →
    w ∈ LinearMap.ker (leafDeck n) →
    (∀ H : RetainedMotif q,
      (motifOperator q n H) w = (profileValue H : ℚ) • w) ∧
      w ∈ observabilityDefect q n

end MathlibPlus.Open.ResearchFormalizationD0079
