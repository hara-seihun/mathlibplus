import MathlibPlus.Open.ResearchFormalization.R1148Claim41323
import MathlibPlus.Open.ResearchFormalization.R1148Claim41326

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim41324

open MathlibPlus.Open.ResearchFormalization.R1148Claim41323
open MathlibPlus.Open.ResearchFormalization.R1148Claim41326

noncomputable section

private def properFiberIndices (B : Set V) : Set F7 :=
  {x | (verticalFiber B x).Nonempty ∧ verticalFiber B x ≠ Set.univ}

private def verticalPeriod (B : Set V) : Prop :=
  ∀ t : F7,
    (fun v : V => (v.1, v.2 + t)) '' B = B

private def fiberDevelopmentAffineImage
    (B : Set V) (p : F7 → F7 → F7) (x : F7) : Prop :=
  ∃ (π : Equiv.Perm F7) (δ : Equiv.Perm F7) (a : F7ˣ) (b : F7),
    (∀ y : F7, π y = p x y) ∧
      normalizedDevelopmentLabel (verticalFiber B x) π δ ∧
        affineImage a b (verticalFiber B x) =
          pointImage π (verticalFiber B x)

/-- The zero- and one-proper-fiber branches of the exact same-sign adjacent
profile.  The proper-fiber set is formed from the actual vertical fibers of
`B`; the development map in the one-fiber branch is the actual vertical part
of the supplied section map, and the transporter is in the reviewed
triangular stabilizer. -/
def zeroAndOneProperFiberBranches_claim41324 : Prop :=
  ∀ (B : Set V) (ε : F7)
    (p q : F7 → F7 → F7) (σ τ : Equiv.Perm V),
    sameSignProfile ε p q σ τ →
      adjacentSetEquation B σ τ →
        let P := properFiberIndices B
        (P = ∅ → verticalPeriod B) ∧
          (P.ncard = 1 →
            (∀ x : F7, x ∈ P →
              fiberDevelopmentAffineImage B p x) ∧
              ∃ φ : Equiv.Perm V,
                φ ∈ triangularLinearStabilizer ∧ φ '' B = σ '' B)

end
end MathlibPlus.Open.ResearchFormalization.R1148Claim41324
