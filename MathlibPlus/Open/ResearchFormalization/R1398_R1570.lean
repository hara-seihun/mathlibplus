import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1398_R1570

abbrev CayleyCarrier := (Fin 3 → ZMod 2) × ZMod 9

def inverseClosedSet {X : Type*} [AddGroup X] (S : Set X) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def cayleyAdjacency (S : Set CayleyCarrier) (x y : CayleyCarrier) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyGraphIsomorphic (S T : Set CayleyCarrier) : Prop :=
  ∃ e : CayleyCarrier ≃ CayleyCarrier,
    ∀ x y,
      cayleyAdjacency S x y ↔
        cayleyAdjacency T (e x) (e y)

def isCIConnectionSet (S : Set CayleyCarrier) : Prop :=
  ∀ (T : Set CayleyCarrier),
    inverseClosedSet T →
    0 ∉ T →
    cayleyGraphIsomorphic S T →
    ∃ α : CayleyCarrier ≃+ CayleyCarrier, α '' S = T

def claim31056 : Prop :=
  ∀ (S : Set CayleyCarrier),
    inverseClosedSet S →
    0 ∉ S →
    Set.ncard S = 17 →
    isCIConnectionSet S

end MathlibPlus.Open.ResearchFormalization.R1398_R1570
