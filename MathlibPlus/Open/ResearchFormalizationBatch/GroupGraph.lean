import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.GroupGraph

noncomputable section

abbrev GElement (m : ℕ) := ZMod m × ZMod 8

def semidirectProductMul (m : ℕ) (x y : GElement m) : GElement m :=
  (x.1 + (if x.2.val % 2 = 0 then y.1 else -y.1), x.2 + y.2)

def oddLiftMember (S : Finset (ZMod m)) (channels : Finset (ZMod 8))
    (z : GElement m) : Prop :=
  z.1 ∈ S ∧ z.2 ∈ channels

def liftedCayleyRelation (S : Finset (ZMod m)) (channels : Finset (ZMod 8))
    (x y : GElement m) : Prop :=
  ∃ z : GElement m, oddLiftMember S channels z ∧ semidirectProductMul m x z = y

def baseCayleyRelation (S : Finset (ZMod m)) (x y : ZMod m) : Prop :=
  ∃ s : ZMod m, s ∈ S ∧ x + s = y

def baseCayleyPresentationIsomorphism
    (f : ZMod m → ZMod m) (S T : Finset (ZMod m)) : Prop :=
  (∀ x y : ZMod m, baseCayleyRelation S x y ↔ baseCayleyRelation T (f x) (f y))

/-- The lifted two-channel relation is preserved by the normalized map. -/
def exactTwoChannelGraphTransfer : Prop :=
  ∀ (m : ℕ), 1 < m → Odd m →
    ∀ (S₁ S₃ T₁ T₃ : Finset (ZMod m))
      (f : ZMod m → ZMod m),
      f 0 = 0 →
      Function.Bijective f →
      baseCayleyPresentationIsomorphism f S₁ T₁ →
      baseCayleyPresentationIsomorphism f S₃ T₃ →
      ∀ x y : GElement m,
        (liftedCayleyRelation S₁ {1, 7} x y ∨
          liftedCayleyRelation S₃ {3, 5} x y) ↔
        (liftedCayleyRelation T₁ {1, 7}
            (f x.1, x.2) (f y.1, y.2) ∨
          liftedCayleyRelation T₃ {3, 5}
            (f x.1, x.2) (f y.1, y.2))

end
end MathlibPlus.Open.ResearchFormalizationBatch.GroupGraph
