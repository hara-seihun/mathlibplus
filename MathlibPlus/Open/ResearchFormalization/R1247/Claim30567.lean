import MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

namespace MathlibPlus.Open.ResearchFormalization.R1247.Claim30567

open MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

noncomputable section

/-- The transvection-generated subgroup and the rotation-section orbit
conclusion in the reviewed derivative carrier. -/
def transvectionsGenerateSL2AndRotationOrbits_claim30567 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    ∀ h : SectionLabel, rotationSection h →
      let transvectionGroup : Subgroup (Equiv.Perm (V p)) :=
        Subgroup.closure
          {d | (∃ a : ZMod p, ∀ v : V p,
                  d v = (v.1, v.2 + a * v.1)) ∨
                (∃ b : ZMod p, ∀ v : V p,
                  d v = (v.1 + b * v.2, v.2))}
      let matrixAction : Matrix (Fin 2) (Fin 2) (ZMod p) → V p → V p :=
        fun M v =>
          (M 0 0 * v.1 + M 0 1 * v.2,
            M 1 0 * v.1 + M 1 1 * v.2)
      transvectionGroup ≤ derivativeGroup p h ∧
        (∀ M : Matrix (Fin 2) (Fin 2) (ZMod p), M.det = 1 →
          ∃ d : transvectionGroup, ∀ v : V p,
            d.1 v = matrixAction M v) ∧
        (∀ d : derivativeGroup p h,
          d.1 (0 : V p) = 0) ∧
        derivativeOrbit p h 0 = ({0} : Set (V p)) ∧
        (∀ v : V p, v ≠ 0 →
          derivativeOrbit p h v = {w | w ≠ 0})

end

end MathlibPlus.Open.ResearchFormalization.R1247.Claim30567
