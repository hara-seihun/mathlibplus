import Mathlib

namespace MathlibPlus.Open.ResearchBatch.ColoredAffine

abbrev V7 := ZMod 7 × ZMod 7
abbrev Color := Fin 5

/-- An inverse-closed five-coloring of the nonzero difference atoms. -/
def InverseClosed (c : V7 → Color) : Prop :=
  ∀ v : V7, c (-v) = c v

/-- The color-preserving condition for the permutation on differences. -/
def IsFiveColoredCayleyIsomorphism
    (f : Equiv.Perm V7) (c d : V7 → Color) : Prop :=
  ∀ x y : V7, x ≠ y → c (x - y) = d (f x - f y)

/-- One link joins the source and target atoms contributed by an unordered pair;
    the other links identify each atom with its inverse. -/
def inverseAtomLink
    (f : Equiv.Perm V7) (v w : Sum V7 V7) : Prop :=
  (∃ x y : V7, x ≠ y ∧
    ((v = Sum.inl (x - y) ∧ w = Sum.inr (f x - f y)) ∨
      (v = Sum.inr (f x - f y) ∧ w = Sum.inl (x - y)))) ∨
  (∃ t : V7,
    (v = Sum.inl t ∧ w = Sum.inl (-t)) ∨
      (v = Sum.inl (-t) ∧ w = Sum.inl t) ∨
      (v = Sum.inr t ∧ w = Sum.inr (-t)) ∨
      (v = Sum.inr (-t) ∧ w = Sum.inr t))

/-- A labeling constant on every link is precisely a labeling of the connected
    components, with the source and target restrictions displayed explicitly. -/
def ComponentLabeling
    (f : Equiv.Perm V7) (c d : V7 → Color) : Prop :=
  ∃ labels : Sum V7 V7 → Color,
    (∀ v w : Sum V7 V7,
      inverseAtomLink f v w → labels v = labels w) ∧
    (∀ v : V7, labels (Sum.inl v) = c v) ∧
    (∀ v : V7, labels (Sum.inr v) = d v) ∧
    Set.ncard (Set.range labels) ≤ 5

/-- The derivative-component criterion for a fixed color isomorphism on `𝔽₇²`. -/
def claim42454 : Prop :=
  ∀ (f : Equiv.Perm V7) (c d : V7 → Color),
    f 0 = 0 →
    InverseClosed c →
    InverseClosed d →
    (IsFiveColoredCayleyIsomorphism f c d ↔ ComponentLabeling f c d)

end MathlibPlus.Open.ResearchBatch.ColoredAffine
