import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1155C41414

noncomputable section

abbrev Boolean := ZMod 2

/-- The pointwise linearity condition defining `L_b`. -/
def linearityCondition {H : Type*} [AddCommGroup H]
    (b : H → Boolean) (h : H) : Prop :=
  ∀ u : H, b (h + u) = b h + b u

/-- The exact linearity set. -/
def linearitySet {H : Type*} [AddCommGroup H]
    (b : H → Boolean) : Set H :=
  {h | linearityCondition b h}

/-- The subgroup carrier agrees with the displayed linearity set. -/
def linearitySubgroupWitness {H : Type*} [AddCommGroup H]
    (b : H → Boolean) (L : AddSubgroup H) : Prop :=
  ∀ h : H, h ∈ L ↔ h ∈ linearitySet b

/-- The restriction of `b` to a subgroup is additive. -/
def restrictionIsHom {H : Type*} [AddCommGroup H]
    (b : H → Boolean) (L : AddSubgroup H) : Prop :=
  ∀ x y : L, b (x.1 + y.1) = b x.1 + b y.1

/-- The extension character kills the odd factor in `A × C₂²`. -/
def oddPartKilled {A : Type*} [AddCommGroup A]
    (χ : (A × (Boolean × Boolean)) →+ Boolean) : Prop :=
  ∀ a : A, χ (a, (0, 0)) = 0

/-- Claim 41414: first for a finite normalized additive carrier the exact
linearity set is a subgroup carrying the restricted character; then, and only
then, for an odd finite factor times `C₂²`, the restriction extends to a
character that kills the odd factor. -/
def claim41414_linearitySubgroupCharacter : Prop :=
  (∀ (H : Type*) [AddCommGroup H] [Fintype H]
      (b : H → Boolean),
      b 0 = 0 →
      ∃ L : AddSubgroup H,
        linearitySubgroupWitness b L ∧
          restrictionIsHom b L) ∧
  (∀ (A : Type*) [AddCommGroup A] [Fintype A],
      Odd (Fintype.card A) →
      let H := A × (Boolean × Boolean)
      ∀ b : H → Boolean, b (0, (0, 0)) = 0 →
        ∃ L : AddSubgroup H,
          linearitySubgroupWitness b L ∧
            restrictionIsHom b L ∧
            ∃ χ : H →+ Boolean,
              (∀ h : L, χ h.1 = b h.1) ∧ oddPartKilled χ)

end

end MathlibPlus.Open.ResearchFormalization.R1155C41414
