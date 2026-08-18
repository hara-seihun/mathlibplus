import MathlibPlus.Open.ResearchFormalization.R2071

namespace MathlibPlus.Open.ResearchFormalization.R2071

noncomputable section

/-- Claim 36023: the actual complete-graph-dual product has `M ^ t` backbone
members and backbone rank `(M - 1) * t`; under the full admissibility range,
the canonical cyclic layer has `M ^ t` coordinates, support size `s` in both
directions, and augmented rank `(M - 1) * t + s`. -/
def claim36023 : Prop :=
  ∀ (M t s : ℕ),
    admissibleParameters M t s →
      cyclicConstructionFacts M t s

end
end MathlibPlus.Open.ResearchFormalization.R2071
