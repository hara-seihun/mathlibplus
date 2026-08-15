import Mathlib

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- The group-ring action and degree-one cocycle spaces for the coprime claim. -/
def groupRingAction {m : ℕ} {H M : Type*} [Group H]
    [AddCommMonoid M] [Module (MonoidAlgebra (ZMod m) H) M]
    (g : H) (x : M) : M :=
  (MonoidAlgebra.single g (1 : ZMod m)) • x

def isOneCocycle {m : ℕ} {H M : Type*} [Group H]
    [AddCommMonoid M] [Module (MonoidAlgebra (ZMod m) H) M]
    (f : H → M) : Prop :=
  ∀ g h, f (g * h) = f g + groupRingAction (m := m) g (f h)

def isCoboundary {m : ℕ} {H M : Type*} [Group H]
    [AddCommGroup M] [Module (MonoidAlgebra (ZMod m) H) M]
    (f : H → M) : Prop :=
  ∃ x : M, ∀ g, f g = groupRingAction (m := m) g x - x

def cocycleSpace {m : ℕ} {H M : Type*} [Group H]
    [AddCommMonoid M] [Module (MonoidAlgebra (ZMod m) H) M] :
    Set (H → M) := {f | isOneCocycle (m := m) f}

def coboundarySpace {m : ℕ} {H M : Type*} [Group H]
    [AddCommGroup M] [Module (MonoidAlgebra (ZMod m) H) M] :
    Set (H → M) := {f | isCoboundary (m := m) f}

def firstCohomologyZero {m : ℕ} {H M : Type*} [Group H]
    [AddCommGroup M] [Module (MonoidAlgebra (ZMod m) H) M] : Prop :=
  ∀ f : H → M, isOneCocycle (m := m) f → isCoboundary (m := m) f

def claim30792 {m : ℕ} {H M : Type*} [Fintype H] [Group H]
    [AddCommGroup M] [Module (MonoidAlgebra (ZMod m) H) M] : Prop :=
  Nat.Coprime (Fintype.card H) m →
    cocycleSpace (m := m) (H := H) (M := M) =
        coboundarySpace (m := m) (H := H) (M := M) ∧
      firstCohomologyZero (m := m) (H := H) (M := M) ∧
      Function.Bijective (fun x : M => (Fintype.card H) • x)
end MathlibPlus.Open.ResearchFormalization.Batch
