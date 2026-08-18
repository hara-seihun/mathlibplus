import MathlibPlus.Open.ResearchFormalization.R1148Claim41323
import MathlibPlus.Open.ResearchFormalization.R1148Claim41326

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim31560

noncomputable section

abbrev F7 := MathlibPlus.Open.ResearchFormalization.R1148Claim41323.F7
abbrev V := MathlibPlus.Open.ResearchFormalization.R1148Claim41323.V

/-- The base coordinates whose vertical fibers are nonempty and proper. -/
def properFiberSet (B : Set V) : Set F7 :=
  {x |
    (MathlibPlus.Open.ResearchFormalization.R1148Claim41323.verticalFiber B x).Nonempty ∧
      MathlibPlus.Open.ResearchFormalization.R1148Claim41323.verticalFiber B x ≠
        (Set.univ : Set F7)}

/-- Every translation in the vertical coordinate is a period of the section. -/
def verticalLinePeriod (B : Set V) : Prop :=
  ∀ t : F7,
    Set.image (fun v : V => v + (0, t)) B = B

/-- A fiber map is a development isomorphism whose fiber image is affine.  No
cardinality restriction is imposed, so singleton and co-singleton fibers are
included. -/
def affineDevelopmentFiberImage
    (B : Set V) (p : F7 → F7 → F7) (x : F7) : Prop :=
  ∃ (π δ : Equiv.Perm F7) (a : F7ˣ) (b : F7),
    (∀ y : F7, π y = p x y) ∧
      MathlibPlus.Open.ResearchFormalization.R1148Claim41326.normalizedDevelopmentLabel
        (MathlibPlus.Open.ResearchFormalization.R1148Claim41323.verticalFiber B x) π δ ∧
        MathlibPlus.Open.ResearchFormalization.R1148Claim41326.affineImage
          a b (MathlibPlus.Open.ResearchFormalization.R1148Claim41323.verticalFiber B x) =
          MathlibPlus.Open.ResearchFormalization.R1148Claim41326.pointImage
            π (MathlibPlus.Open.ResearchFormalization.R1148Claim41323.verticalFiber B x)

/-- Zero- and one-proper-fiber branches for the exact same-sign adjacent
section equation. -/
def claim31560 : Prop :=
  ∀ (B : Set V) (ε : F7)
    (p q : F7 → F7 → F7)
    (σ τ : Equiv.Perm V),
    MathlibPlus.Open.ResearchFormalization.R1148Claim41323.sameSignProfile
        ε p q σ τ →
      MathlibPlus.Open.ResearchFormalization.R1148Claim41323.adjacentSetEquation
        B σ τ →
      let P := properFiberSet B
      (P = ∅ → verticalLinePeriod B) ∧
        (Set.ncard P = 1 →
          (∀ x : F7, x ∈ P → affineDevelopmentFiberImage B p x) ∧
            ∃ φ : Equiv.Perm V,
              φ ∈
                  MathlibPlus.Open.ResearchFormalization.R1148Claim41323.triangularLinearStabilizer ∧
                φ '' B = σ '' B)

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim31560
