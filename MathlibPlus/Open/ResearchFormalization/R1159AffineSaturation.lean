import MathlibPlus.Open.ResearchFormalization.R1159.Claim41462

namespace MathlibPlus.Open.ResearchFormalization.R1159AffineSaturation

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1159.Claim41462

/-- Claim 31695: in an exact scalar-quiet component, either two loops with
the same nontrivial multiplier have distinct affine centers, or their
commutator is a nonzero translation; in either case the generated affine
subgroup contains every translation of the prime fibre. -/
def distinctCentersForceAffineSaturation_claim31695 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (ω : (ZMod p)ˣ) (σ : Equiv.Perm SThree)
      (e : SThree → ZMod 3) (τ : SThree → ZMod p)
      (L : Set (AffineLoop p)),
      scalarQuietComponent ω σ e τ L →
        ∀ (f g : AffineLoop p),
          f ∈ L → g ∈ L →
            ((∃ (a : (ZMod p)ˣ) (b d c₁ c₂ : ZMod p),
                a ≠ 1 ∧
                  affineLoopForm f a b ∧
                    affineLoopForm g a d ∧
                      commonCenterEquation a b c₁ ∧
                        commonCenterEquation a d c₂ ∧ c₁ ≠ c₂) ∨
              (∃ t : ZMod p, t ≠ 0 ∧
                ∀ z : ZMod p,
                  (f * g * f.symm * g.symm) z = z + t)) →
              affineComponentSaturated L

end

end MathlibPlus.Open.ResearchFormalization.R1159AffineSaturation
