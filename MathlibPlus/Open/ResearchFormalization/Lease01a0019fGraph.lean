import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

/-- The trunk attachment factor at a positive distance. -/
def trunkAttachmentFactor (d : ℕ) (z : ℝ) : ℝ := z ^ d * (1 - z)

def claim29411 : Prop :=
  ∀ d : ℕ, 0 < d → ∀ z : ℝ,
    trunkAttachmentFactor d z = z ^ d * (1 - z)

/-- The leaf-corona operation on a simple graph. -/
def leafCorona {V : Type} (T : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inl b => T.Adj a b
    | Sum.inl a, Sum.inr b => a = b
    | Sum.inr a, Sum.inl b => a = b
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro x y h
    cases x with
    | inl a =>
        cases y with
        | inl b => exact T.symm.symm a b h
        | inr b => exact h.symm
    | inr a =>
        cases y with
        | inl b => exact h.symm
        | inr b => exact False.elim h⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl a => exact T.loopless.irrefl a h
    | inr a => exact False.elim h⟩

/-- Adjoining one pendant leaf at every vertex doubles the finite vertex set
 and preserves the tree property; the polymorphic operation is globally
 iterable. -/
def claim28281 : Prop :=
  ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
    T.IsTree →
      (leafCorona T).IsTree ∧
        Fintype.card (V ⊕ V) = 2 * Fintype.card V

end
end MathlibPlus.Open.ResearchFormalization.Batch01
