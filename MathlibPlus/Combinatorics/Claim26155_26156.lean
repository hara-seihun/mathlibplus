import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Combinatorics.R0554

/-- Claim 26155: zero triangle parity is exactly an additive coboundary on a
complete graph over `F₂`. -/
def zeroTriangleParityCoboundary_claim26155 : Prop :=
  ∀ (α : Type*) [Fintype α] (s : α → α → ZMod 2),
    (∀ u, s u u = 0) →
    (∀ u v, s u v = s v u) →
    ((∀ ⦃u v w : α⦄, u ≠ v → v ≠ w → u ≠ w →
        s u v + s u w + s v w = 0) ↔
      ∃ x : α → ZMod 2,
        ∀ ⦃u v : α⦄, u ≠ v → s u v = x u + x v)

/-- Claim 26156: one triangle parity is exactly the antibalanced class,
without excluding small complete graphs. -/
def oneTriangleParityAntibalanced_claim26156 : Prop :=
  ∀ (α : Type*) [Fintype α] (s : α → α → ZMod 2),
    (∀ u, s u u = 0) →
    (∀ u v, s u v = s v u) →
    ((∀ ⦃u v w : α⦄, u ≠ v → v ≠ w → u ≠ w →
        s u v + s u w + s v w = 1) ↔
      ∃ x : α → ZMod 2,
        ∀ ⦃u v : α⦄, u ≠ v → s u v + 1 = x u + x v)

end MathlibPlus.Combinatorics.R0554
