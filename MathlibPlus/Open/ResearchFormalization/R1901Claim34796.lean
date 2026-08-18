import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1901Claim34796

noncomputable section

/-- Translation of a finite subset by a displacement in the additive
    F₂-vector-space carrier. -/
def translateFinset {W : Type*} [Add W] [DecidableEq W]
    (S : Finset W) (v : W) : Finset W :=
  S.image (fun x => x + v)

/-- Both coordinate projections of a relation are onto. -/
def relationProjectionsSurjective {W : Type*} (L : Set (W × W)) : Prop :=
  (∀ x : W, ∃ y : W, (x, y) ∈ L) ∧
    (∀ y : W, ∃ x : W, (x, y) ∈ L)

/-- Claim 34796: the finite F₂ relation lemma with the exact joint
    displacement-avoidance hypothesis and the sharp half-cardinality bound. -/
def finiteRelationLemmaClaim : Prop :=
  ∀ {W : Type*} [Fintype W] [AddCommGroup W] [Module (ZMod 2) W],
    letI : DecidableEq W := Classical.decEq W
    ∀ (S : Finset W) (a b : W) (L : AddSubgroup (W × W)),
      relationProjectionsSurjective (L : Set (W × W)) →
        (a, b) ∈ L →
        (∀ x y : W, (x, y) ∈ L →
          ∃ z : W, (x, z) ∈ L ∧ (y, z) ∈ L) →
        (∀ x ∈ S ∩ translateFinset S a,
          ∀ y ∈ S ∩ translateFinset S b,
            (x, y) ∉ L) →
        2 * S.card ≤ Fintype.card W

end

end MathlibPlus.Open.ResearchFormalization.R1901Claim34796
