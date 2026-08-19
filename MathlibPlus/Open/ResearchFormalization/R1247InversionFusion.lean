import MathlibPlus.Open.ResearchFormalization.R1247.Claim30572

namespace MathlibPlus.Open.ResearchFormalization.R1247InversionFusion

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1247.Claim30572

/-- Claim 30570: on the exact `V × S₃` carrier, inversion fuses the nine
sectionwise derivative orbits into the seven explicit blocks, preserves their
zero/nonzero and reflection-fibre distinctions, and produces no additional
fusion for inverse-closed derivative-invariant sets. -/
def inversionCompatibilityFusesSevenBlocks_claim30570 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    Set.ncard (sevenBlocks p) = 7 ∧
      (∀ C ∈ sevenBlocks p,
        Set.image (pointInverse p) C = C) ∧
      (∀ S : Set (Point p),
        S ⊆ {z | z ≠ pointIdentity p} →
          inverseClosedPointSet p S →
            inverseClosedPointSet p (Set.image (markedMap p) S) →
              (∀ d : Equiv.Perm (Point p),
                fullDerivativeGenerator p d → Set.image d S = S) →
                unionOfSevenBlocks p S)

end

end MathlibPlus.Open.ResearchFormalization.R1247InversionFusion
