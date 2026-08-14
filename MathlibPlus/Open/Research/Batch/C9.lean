import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch.C9

/-- The inverse-closed subsets and the three distinguished sectors of `C₉`. -/
def inverseClosedC9 (D : Finset (ZMod 9)) : Prop :=
  ∀ x : ZMod 9, x ∈ D ↔ -x ∈ D

def c9Units : Finset (ZMod 9) :=
  Finset.univ.filter (fun x : ZMod 9 => Nat.Coprime x.val 9)

def c9H0 : Finset (ZMod 9) := {0, 3, 6}

noncomputable def c9PrimitiveSum (D : Finset (ZMod 9)) : ℂ :=
  ∑ x : ZMod 9,
    if x ∈ D then
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I * ((x.val : ℂ) / 9))
    else 0

noncomputable def c9OrderThreeSum (D : Finset (ZMod 9)) : ℂ :=
  ∑ x : ZMod 9,
    if x ∈ D then
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I * ((x.val : ℂ) / 3))
    else 0

def c9RationalPrimitiveFamily : Finset (Finset (ZMod 9)) :=
  (Finset.univ : Finset (Bool × Bool × Bool)).image
    (fun b =>
      (if b.1 then ({0} : Finset (ZMod 9)) else ∅) ∪
        (if b.2.1 then c9H0 \ {0} else ∅) ∪
        (if b.2.2 then c9Units else ∅))

def c9EqualCharacterFamily : Finset (Finset (ZMod 9)) :=
  ({∅, ({0} : Finset (ZMod 9)),
      (Finset.univ : Finset (ZMod 9)) \ {0},
      (Finset.univ : Finset (ZMod 9))} : Finset (Finset (ZMod 9)))

noncomputable def c9Fingerprint (D : Finset (ZMod 9)) : ℂ :=
  c9PrimitiveSum D - c9OrderThreeSum D

/-- Exact ninth-root character classification, including the two character
comparisons and the fifteen-valued fingerprint. -/
def ninthRootCharacterClassificationClaim58962 : Prop := by
  classical
  exact let allInverseClosed : Finset (Finset (ZMod 9)) :=
    (Finset.univ : Finset (Finset (ZMod 9))).filter inverseClosedC9
  let rationalInverseClosed :=
    allInverseClosed.filter (fun D =>
      ∃ q : ℚ, c9PrimitiveSum D = (q : ℂ))
  let equalInverseClosed :=
    allInverseClosed.filter (fun D => c9PrimitiveSum D = c9OrderThreeSum D)
  rationalInverseClosed.card = 8 ∧
    (∀ D : Finset (ZMod 9),
      inverseClosedC9 D →
      ((∃ q : ℚ, c9PrimitiveSum D = (q : ℂ)) ↔
        D ∈ c9RationalPrimitiveFamily)) ∧
    equalInverseClosed.card = 4 ∧
    (∀ D : Finset (ZMod 9),
      inverseClosedC9 D →
      (c9PrimitiveSum D = c9OrderThreeSum D ↔
        D ∈ c9EqualCharacterFamily)) ∧
    allInverseClosed.card = 32 ∧
    (Finset.image c9Fingerprint allInverseClosed).card = 15

end MathlibPlus.Open.ResearchBatch.C9
