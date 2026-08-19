import MathlibPlus.Algebra.TranslationPeriodFunctor
import MathlibPlus.GraphTheory.LeftTranslationStabilizerQuotientCI

namespace MathlibPlus.Open.ResearchFormalization.Claim61356

noncomputable section

open scoped Pointwise
open MathlibPlus.Algebra.TranslationPeriod

universe uG uH uX uY

/-- The general multiplicative stabilizer pullback along a surjective
 equivariant map. -/
def equivariantStabilizerPullback : Prop :=
  ∀ {G : Type uG} {H : Type uH} {X : Type uX} {Y : Type uY}
    [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (φ : G →* H) (q : X → Y),
    Function.Surjective q →
      (∀ g x, q (g • x) = φ g • q x) →
        ∀ S : Set Y,
          MulAction.stabilizer G (q ⁻¹' S) =
            (MulAction.stabilizer H S).comap φ

/-- The additive version of the equivariant stabilizer pullback. -/
def additiveEquivariantStabilizerPullback : Prop :=
  ∀ {G : Type uG} {H : Type uH} {X : Type uX} {Y : Type uY}
    [AddGroup G] [AddGroup H] [AddAction G X] [AddAction H Y]
    (φ : G →+ H) (q : X → Y),
    Function.Surjective q →
      (∀ g x, q (g +ᵥ x) = φ g +ᵥ q x) →
        ∀ S : Set Y,
          AddAction.stabilizer G (q ⁻¹' S) =
            (AddAction.stabilizer H S).comap φ

/-- The translation-period carrier is the regular additive-action
stabilizer carrier. -/
def regularAdditivePeriodIdentification : Prop :=
  ∀ {B : Type uG} [AddCommGroup B] (X : Set B),
    periodSubgroup X = AddAction.stabilizer B X

/-- The additive quotient specialization. -/
def additiveQuotientPeriodPullback : Prop :=
  ∀ {B : Type uG} [AddCommGroup B]
    (N : AddSubgroup B) (S : Set (B ⧸ N)),
    periodSubgroup ((QuotientAddGroup.mk' N) ⁻¹' S) =
      (periodSubgroup S).comap (QuotientAddGroup.mk' N)

/-- The multiplicative quotient specialization. -/
def multiplicativeQuotientStabilizerPullback : Prop :=
  ∀ {G : Type uG} [Group G]
    (N : Subgroup G) [N.Normal] (S : Set (G ⧸ N)),
    MulAction.stabilizer G ((QuotientGroup.mk' N) ⁻¹' S) =
      (MulAction.stabilizer (G ⧸ N) S).comap (QuotientGroup.mk' N)

/-- Claim 61356: the common equivariant-preimage stabilizer theorem, its
additive form, and the regular-additive and quotient specializations. -/
def claim61356 : Prop :=
  (∀ {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y]
    (φ : G →* H) (q : X → Y),
    Function.Surjective q →
      (∀ g x, q (g • x) = φ g • q x) →
        ∀ S : Set Y,
          MulAction.stabilizer G (q ⁻¹' S) =
            (MulAction.stabilizer H S).comap φ) ∧
    (∀ {G H X Y : Type*} [AddGroup G] [AddGroup H]
      [AddAction G X] [AddAction H Y]
      (φ : G →+ H) (q : X → Y),
      Function.Surjective q →
        (∀ g x, q (g +ᵥ x) = φ g +ᵥ q x) →
          ∀ S : Set Y,
            AddAction.stabilizer G (q ⁻¹' S) =
              (AddAction.stabilizer H S).comap φ) ∧
      (∀ {B : Type*} [AddCommGroup B] (X : Set B),
        periodSubgroup X = AddAction.stabilizer B X) ∧
        (∀ {B : Type*} [AddCommGroup B]
          (N : AddSubgroup B) (S : Set (B ⧸ N)),
          periodSubgroup ((QuotientAddGroup.mk' N) ⁻¹' S) =
            (periodSubgroup S).comap (QuotientAddGroup.mk' N)) ∧
          (∀ {G : Type*} [Group G]
            (N : Subgroup G) [N.Normal] (S : Set (G ⧸ N)),
            MulAction.stabilizer G ((QuotientGroup.mk' N) ⁻¹' S) =
              (MulAction.stabilizer (G ⧸ N) S).comap (QuotientGroup.mk' N))

end

end MathlibPlus.Open.ResearchFormalization.Claim61356
