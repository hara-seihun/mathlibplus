import Mathlib

noncomputable section
open Classical
attribute [local instance] Classical.propDecidable

namespace MathlibPlus.Open.ResearchBatch.Wreath

abbrev wreathOmega (Delta Lambda : Type*) := Delta × Lambda

def preservesFibrePartition {Delta Lambda : Type*}
    (w : Equiv.Perm (wreathOmega Delta Lambda)) : Prop :=
  ∀ d : Delta, ∃ d' : Delta, ∀ l : Lambda,
    (w (d, l)).1 = d'

def fullFibreWreathGroup {Delta Lambda : Type*} :
    Subgroup (Equiv.Perm (wreathOmega Delta Lambda)) :=
  Subgroup.closure {w | preservesFibrePartition w}

def regularWreathCopy {A H Delta Lambda : Type*}
    [Fintype A] [Fintype H] [Fintype Delta] [Fintype Lambda]
    [CommGroup A] [Group H]
    (K : Subgroup (Equiv.Perm (wreathOmega Delta Lambda))) : Prop :=
  K ≤ fullFibreWreathGroup ∧
    Nonempty ((A × H) ≃* K) ∧
      ∀ x y : wreathOmega Delta Lambda, ∃! k : K, k.1 x = y

def conjugateWreathCopies {Delta Lambda : Type*}
    (W : Subgroup (Equiv.Perm (wreathOmega Delta Lambda)))
    (R T : Subgroup (Equiv.Perm (wreathOmega Delta Lambda))) : Prop :=
  ∃ w : W, ∀ t : Equiv.Perm (wreathOmega Delta Lambda), t ∈ T ↔
    ∃ r : Equiv.Perm (wreathOmega Delta Lambda), r ∈ R ∧
      t = w.1 * r * w.1⁻¹

/-- Coprime regular copies are conjugate in the full-fibre wreath action. -/
def claim45601 : Prop :=
  ∀ (A H Delta Lambda : Type*)
    [Fintype A] [Fintype H] [Fintype Delta] [Fintype Lambda]
    [CommGroup A] [Group H],
    Nat.Coprime (Fintype.card A) (Fintype.card H) →
      Fintype.card Delta = Fintype.card A →
      Fintype.card Lambda = Fintype.card H →
      ∀ R T : Subgroup (Equiv.Perm (wreathOmega Delta Lambda)),
        regularWreathCopy (A := A) (H := H) (Delta := Delta) (Lambda := Lambda) R →
        regularWreathCopy (A := A) (H := H) (Delta := Delta) (Lambda := Lambda) T →
          conjugateWreathCopies (fullFibreWreathGroup :
            Subgroup (Equiv.Perm (wreathOmega Delta Lambda))) R T

end MathlibPlus.Open.ResearchBatch.Wreath
