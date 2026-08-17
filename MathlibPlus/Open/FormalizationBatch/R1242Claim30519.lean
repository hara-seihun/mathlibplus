import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R1242Claim30519

noncomputable section

abbrev F3 := ZMod 3
abbrev Plane := Fin 2 → F3
abbrev Vector := Fin 3 → F3
abbrev Table := Plane → Vector

def ell (x : Plane) : Vector :=
  fun k => if k = 0 then x 1 ^ 2 else if k = 1 then -(x 0 * x 1) else x 0 ^ 2

def delta (x : Plane) (F : Table) (s : Plane) : Vector :=
  F (s + x) - F s

def recurrenceSet (x : Plane) (H : Plane → F3) (t : F3) : Set Table :=
  {F | F 0 = 0 ∧ ∀ s : Plane, delta x F s = t • (H s • ell x)}

def affineSixSpace (A : Set Table) : Prop :=
  ∃ (a : Table) (W : Submodule F3 Table),
    Module.finrank F3 W = 6 ∧
      A = {y : Table | ∃ w : Table, w ∈ W ∧ y = a + w}

/-- Claim 30519: after retaining the aligned periodic `H` profile, the three
normalized recurrence classes are disjoint affine six-spaces of size 729 and
have total size 2187. -/
def claim30519_disjointAffineSixSpaces : Prop :=
  ∀ (x : Plane), ell x ≠ 0 →
    ∀ (H : Plane → F3), H ≠ 0 →
      (∀ s : Plane, H (s + x) = H s) →
      (∀ ⦃t t' : F3⦄ ⦃F : Table⦄,
        t ≠ t' → F ∈ recurrenceSet x H t → F ∈ recurrenceSet x H t' →
          ∀ s : Plane, (t - t') • (H s • ell x) = 0) ∧
      (∀ t : F3, affineSixSpace (recurrenceSet x H t)) ∧
      (∀ t : F3,
        Nat.card {F : Table // F ∈ recurrenceSet x H t} = 729) ∧
      (∀ ⦃t t' : F3⦄, t ≠ t' →
        Disjoint (recurrenceSet x H t) (recurrenceSet x H t')) ∧
      Nat.card {F : Table // F ∈ ⋃ t : F3, recurrenceSet x H t} = 2187

end

end MathlibPlus.Open.FormalizationBatch.R1242Claim30519
