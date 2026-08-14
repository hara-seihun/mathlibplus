import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The inverse-closed subsets and the three distinguished sectors of `C₉`. -/
def inverseClosedC9Research (D : Finset (ZMod 9)) : Prop :=
  ∀ x : ZMod 9, x ∈ D ↔ -x ∈ D

def c9UnitsResearch : Finset (ZMod 9) :=
  Finset.univ.filter (fun x : ZMod 9 => Nat.Coprime x.val 9)

def c9H0Research : Finset (ZMod 9) := {0, 3, 6}

def c9PrimitiveSumResearch (D : Finset (ZMod 9)) : ℂ :=
  D.sum (fun x =>
    Complex.exp ((2 : ℂ) * Real.pi * Complex.I * ((x.val : ℂ) / 9)))

def c9OrderThreeSumResearch (D : Finset (ZMod 9)) : ℂ :=
  D.sum (fun x =>
    Complex.exp ((2 : ℂ) * Real.pi * Complex.I * ((x.val : ℂ) / 3)))

def c9RationalPrimitiveFamilyResearch : Finset (Finset (ZMod 9)) :=
  (Finset.univ : Finset (Bool × Bool × Bool)).image
    (fun b =>
      (if b.1 then ({0} : Finset (ZMod 9)) else ∅) ∪
        (if b.2.1 then c9H0Research \ {0} else ∅) ∪
        (if b.2.2 then c9UnitsResearch else ∅))

def c9EqualCharacterFamilyResearch : Finset (Finset (ZMod 9)) :=
  ({∅, ({0} : Finset (ZMod 9)),
      (Finset.univ : Finset (ZMod 9)) \ {0},
      (Finset.univ : Finset (ZMod 9))} : Finset (Finset (ZMod 9)))

def c9IndicatorResearch (D : Finset (ZMod 9)) (x : ZMod 9) : ℤ :=
  if x ∈ D then 1 else 0

def c9ConvolutionResearch (f g : ZMod 9 → ℤ) (z : ZMod 9) : ℤ :=
  ∑ x : ZMod 9, f x * g (z - x)

/-- Rational primitive sums, primitive/order-three equality, and the exact
integral group-ring multiplication table for the three cyclic sectors. -/
def exactLocalC9RationalCalculus : Prop := by
  classical
  exact let allInverseClosed : Finset (Finset (ZMod 9)) :=
    (Finset.univ : Finset (Finset (ZMod 9))).filter inverseClosedC9Research
  let rationalInverseClosed :=
    allInverseClosed.filter (fun D =>
      ∃ q : ℚ, c9PrimitiveSumResearch D = (q : ℂ))
  let equalInverseClosed :=
    allInverseClosed.filter
      (fun D => c9PrimitiveSumResearch D = c9OrderThreeSumResearch D)
  rationalInverseClosed.card = 8 ∧
    (∀ D : Finset (ZMod 9),
      inverseClosedC9Research D →
      ((∃ q : ℚ, c9PrimitiveSumResearch D = (q : ℂ)) ↔
        D ∈ c9RationalPrimitiveFamilyResearch)) ∧
    equalInverseClosed.card = 4 ∧
    (∀ D : Finset (ZMod 9),
      inverseClosedC9Research D →
      (c9PrimitiveSumResearch D = c9OrderThreeSumResearch D ↔
        D ∈ c9EqualCharacterFamilyResearch)) ∧
    (∀ z : ZMod 9,
      c9ConvolutionResearch (c9IndicatorResearch c9UnitsResearch)
        (c9IndicatorResearch c9UnitsResearch) z =
        6 * c9IndicatorResearch c9H0Research z +
          3 * c9IndicatorResearch c9UnitsResearch z) ∧
    (∀ z : ZMod 9,
      c9ConvolutionResearch (c9IndicatorResearch c9UnitsResearch)
        (c9IndicatorResearch c9H0Research) z =
        3 * c9IndicatorResearch c9UnitsResearch z) ∧
    (∀ z : ZMod 9,
      c9ConvolutionResearch (c9IndicatorResearch c9H0Research)
        (c9IndicatorResearch c9H0Research) z =
        3 * c9IndicatorResearch c9H0Research z)

end

end MathlibPlus.Open.Algebra
