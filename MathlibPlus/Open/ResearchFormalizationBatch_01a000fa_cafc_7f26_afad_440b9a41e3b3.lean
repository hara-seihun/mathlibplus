import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Translation of a subset of an additive group by a point. -/
def translateSet {V : Type*} [AddGroup V] (X : Set V) (u : V) : Set V :=
  (fun x : V => x + u) '' X

/-- The fibre of a subset of the direct product over its second coordinate. -/
def fibre {V H : Type*} (S : Set (V × H)) (h : H) : Set V :=
  {v | (v, h) ∈ S}

/-- The fibre-preserving map specified by the family of permutations. -/
def presentationMap {V H : Type*} (q : H → Equiv.Perm V) : V × H → V × H :=
  fun p => (q p.2 p.1, p.2)

/-- Inverse closure in the direct product of an additive group and a group. -/
def inverseClosed {V H : Type*} [AddGroup V] [Group H] (S : Set (V × H)) : Prop :=
  ∀ ⦃v : V⦄ ⦃h : H⦄, (v, h) ∈ S → (-v, h⁻¹) ∈ S

/-- Exponent two for an additive group. -/
def exponentTwo {V : Type*} [AddGroup V] : Prop :=
  ∀ v : V, v + v = 0

/-- Exponent three, in the sense used for the finite group in the claim. -/
def exponentThree {H : Type*} [Group H] : Prop :=
  (∀ h : H, h ^ 3 = 1) ∧ ∃ h : H, h ≠ 1

/-- The normalized relative derivative in the direct-product coordinates of the packet. -/
def normalizedRelativeDerivative
    {V H : Type*} [AddGroup V] [Group H]
    (q : H → Equiv.Perm V) (a : H) (u : V) : V × H → V × H :=
  fun p => (q (p.2 * a) (p.1 + u) - q a u, p.2)

/-- Invariance under all normalized relative derivatives, expressed by their set action. -/
def normalizedRelativeDerivativeInvariant
    {V H : Type*} [AddGroup V] [Group H]
    (q : H → Equiv.Perm V) (S : Set (V × H)) : Prop :=
  ∀ (a : H) (u : V),
    normalizedRelativeDerivative q a u '' S = presentationMap q '' S

/-- Claim 41248. -/
def claim41248
    {V H : Type*} [AddCommGroup V] [Group H]
    (q : H → Equiv.Perm V) (S : Set (V × H)) : Prop :=
  exponentTwo (V := V) →
    normalizedRelativeDerivativeInvariant q S →
      ∀ (h a : H) (u : V),
        translateSet
            (q (h * a) '' translateSet (fibre S h) u)
            (q a u) =
          q h '' fibre S h

/-- Claim 41251. -/
def claim41251
    {V H : Type*} [AddCommGroup V] [Group H]
    (q : H → Equiv.Perm V) (S : Set (V × H)) : Prop :=
  exponentTwo (V := V) →
    exponentThree (H := H) →
      q 1 = Equiv.refl V →
        normalizedRelativeDerivativeInvariant q S →
          ∀ (h : H), h ≠ 1 →
            let X := fibre S h
            let Y := q h '' X
            q (h⁻¹) '' X = Y →
              translateSet Y (q h 0) = Y

/-- Claim 41252. -/
def claim41252
    {V H : Type*} [AddCommGroup V] [Group H]
    (q : H → Equiv.Perm V) (S : Set (V × H)) : Prop :=
  exponentTwo (V := V) →
    exponentThree (H := H) →
      q 1 = Equiv.refl V →
        normalizedRelativeDerivativeInvariant q S →
          ∀ (h : H), h ≠ 1 →
            let X := fibre S h
            let Y := q h '' X
            q (h⁻¹) '' X = Y →
              translateSet X (q (h⁻¹) 0) = Y ∧
                (∀ u : V, translateSet X u = X ↔ translateSet Y u = Y) ∧
                  translateSet Y (q h 0) = Y ∧
                    translateSet X (q h 0) = X

/-- Claim 41253. -/
def claim41253
    {V H : Type*} [AddCommGroup V] [Group H]
    (q : H → Equiv.Perm V) (S : Set (V × H)) : Prop :=
  exponentTwo (V := V) →
    exponentThree (H := H) →
      q 1 = Equiv.refl V →
        normalizedRelativeDerivativeInvariant q S →
          inverseClosed S →
            inverseClosed (presentationMap q '' S) →
              ∀ (h : H), h ≠ 1 →
                let X := fibre S h
                let Y := q h '' X
                Y = X ∧ q h '' X = X

/-- Claim 41254. -/
def claim41254
    (V H : Type*) [Fintype V] [AddCommGroup V]
    [Fintype H] [Group H]
    (q : H → Equiv.Perm V) (S : Set (V × H)) : Prop :=
  exponentTwo (V := V) →
    exponentThree (H := H) →
      q 1 = Equiv.refl V →
        normalizedRelativeDerivativeInvariant q S →
          inverseClosed S →
            inverseClosed (presentationMap q '' S) →
              presentationMap q '' S = S

end MathlibPlus.Open.ResearchFormalizationBatch
