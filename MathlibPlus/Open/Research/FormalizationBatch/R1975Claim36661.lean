import Mathlib

noncomputable section
open Classical

namespace MathlibPlus.Open.Research.FormalizationBatch.R1975

/-- The coordinates of the balanced complete-support system are the supports
of cardinality `floor (m/2)` on the member index set `Fin m`. -/
def balancedSupport (m : ℕ) (S : Finset (Fin m)) : Prop :=
  S.card = m / 2

def balancedCoordinateSet (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (balancedSupport m)

/-- The member indexed by `i` contains exactly the coordinates whose supports
contain `i`. -/
def balancedMember (m : ℕ) (i : Fin m) : Finset (Finset (Fin m)) :=
  (balancedCoordinateSet m).filter (fun S => i ∈ S)

/-- Every already queried coordinate is constant on the residual member class. -/
def queriedConstantOnClass {m : ℕ}
    (C : Finset (Fin m)) (queried : Finset (Finset (Fin m))) : Prop :=
  ∀ S ∈ queried,
    (∀ i ∈ C, i ∈ S) ∨ (∀ i ∈ C, i ∉ S)

/-- The exact trace of a member `j` on a fixed pivot member `pivot`. -/
def exactPivotTrace (m : ℕ) (pivot j : Fin m) : Finset (Finset (Fin m)) :=
  balancedMember m pivot ∩ balancedMember m j

/-- Claim 36661: balanced complete-support residual classes have a new
one-third splitter in the two stated construction cases, and distinct
nonpivot members have distinct traces when compared on a fixed pivot. -/
def claim36661 : Prop :=
  (∀ m : ℕ, ∀ C : Finset (Fin m),
      ∀ queried : Finset (Finset (Fin m)),
      2 ≤ C.card →
      (∀ S ∈ queried, balancedSupport m S) →
      queriedConstantOnClass C queried →
      ∃ S : Finset (Fin m),
        balancedSupport m S ∧
        (((C.card - 1 ≤ m / 2) ∧
            (S ∩ C).card = C.card - 1) ∨
          ((m / 2 < C.card - 1) ∧ S ⊆ C ∧
            (S ∩ C).card = m / 2)) ∧
        (C.card : ℚ) / 3 ≤ ((S ∩ C).card : ℚ) ∧
        ((S ∩ C).card : ℚ) < (C.card : ℚ) ∧
        S ∉ queried) ∧
  (∀ m : ℕ, ∀ pivot : Fin m,
      ∀ j k : Fin m,
        j ≠ pivot → k ≠ pivot → j ≠ k →
          exactPivotTrace m pivot j ≠ exactPivotTrace m pivot k)

end MathlibPlus.Open.Research.FormalizationBatch.R1975
