import MathlibPlus.Open.ResearchFormalization.EdgeCountConsequenceClaim35571

namespace MathlibPlus.Open.ResearchFormalization.NearLogOrbitClaim35539

open Filter
open Asymptotics
open MathlibPlus.Open.ResearchFormalization.EdgeCountConsequenceClaim35571

noncomputable section

/-- The o(n) directional-mass conclusion in the literal edge-system carrier. -/
def littleLinearError35539 (s : ℕ → ℝ) : Prop :=
  ∃ e : ℕ → ℝ,
    IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop,
        s n ≤ ((1 / 2 : ℝ) + e n) * (n : ℝ)

/-- The directional and edge-count conclusions of the near-logarithmic
orbit theorem. -/
def nearLogConclusion35539 (F : EdgeSystemFamily) : Prop :=
  littleLinearError35539 (directionalMass F) ∧
    edgeMassIdentity F ∧
    littleEdgeFactor F

/-- Claim 35539: literal directional translation-orbit control gives the
near-half directional mass and hence the edge-count consequence, both under
the little-o logarithmic regime and under the stated explicit logarithmic
regime. -/
def nearLogarithmicOrbitTheorem_claim35539 : Prop :=
  ∀ (F : EdgeSystemFamily) (M : ℕ → ℕ),
    familyC4Free F →
      familyOrbitBound F M →
        (orbitLogCondition M →
          nearLogConclusion35539 F) ∧
        (∀ ε : ℝ,
          0 < ε →
            ε < 1 / 2 →
              explicitOrbitCondition M ε →
                nearLogConclusion35539 F)

end

end MathlibPlus.Open.ResearchFormalization.NearLogOrbitClaim35539
