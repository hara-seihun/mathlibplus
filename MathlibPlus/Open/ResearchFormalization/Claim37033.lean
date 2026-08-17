import MathlibPlus.Open.ResearchFormalization.Claim37034

open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- Claim 37033: the nested-shell family has the exact first peel and moat
limits, with the retained core strictly inside the outer filled polygon and
with the support/inradius bounds on its largest admissible moat width. -/
def claim37033 : Prop :=
  (∀ᶠ k : ℕ in atTop,
    let m := oddShellIndex k
    retainedCore m ⊂ polygonRegion m ∧
      firstPeelExact m ∧
      polygonInradius m - polygonRadius (m - 8) ≤ moatWidth m ∧
      moatWidth m ≤ polygonRadius m - polygonRadius (m - 8)) ∧
    Tendsto
      (fun k : ℕ => firstPeelLoss (oddShellIndex k))
      atTop (𝓝 (8 / Real.pi)) ∧
    Tendsto
      (fun k : ℕ => moatWidth (oddShellIndex k))
      atTop (𝓝 (4 / Real.pi))

end

end MathlibPlus.Open.ResearchFormalization
