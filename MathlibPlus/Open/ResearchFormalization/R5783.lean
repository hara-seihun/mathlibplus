import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R5783

noncomputable section

/-- The cubic map in R-5783.1, with the three coordinates represented by
`Fin 3 → ZMod p`. -/
def henonF (p : ℕ) (z : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

/-- The coupled map from R-5783.1. -/
def coupledQ {W : Type*} (p : ℕ)
    (x z : Fin 3 → ZMod p) (w : W) :
    (Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W :=
  (z, x + henonF p z, w)

/-- The linear comparison map from R-5783.1. -/
def linearShadow {W : Type*}
    (x z : Fin 3 → ZMod p) (w : W) :
    (Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W :=
  (z, x, w)

/-- R-5783.1: the displayed coupled map and its coordinate-swap linear
comparison, for every odd prime in the stated range and every finite passive
vector space.  The equations are retained as the mathematical content of the
setup rather than replacing the named maps by an opaque predicate. -/
def claim58492 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p →
    ∀ (W : Type*) [Fintype W] [AddCommGroup W] [Module (ZMod p) W]
      (x z : Fin 3 → ZMod p) (w : W),
      coupledQ p x z w = (z, x + henonF p z, w) ∧
        linearShadow x z w = (z, x, w)

/-- The mixed difference set in R-5783.2. -/
def mixedDifference (p : ℕ) (d z : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  henonF p (z + d) - henonF p z - henonF p d

def mixedDifferenceSet (p : ℕ) (d : Fin 3 → ZMod p) :
    Set (Fin 3 → ZMod p) :=
  Set.range (mixedDifference p d)

def mixedDifferenceSpan (p : ℕ) (d : Fin 3 → ZMod p) :
    Submodule (ZMod p) (Fin 3 → ZMod p) :=
  Submodule.span (ZMod p) (mixedDifferenceSet p d)

def mixedDifferenceFormula (p : ℕ)
    (d z : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  ![
    2 * d 0 * z 0 + d 0 * z 1 * z 2 + d 1 * z 0 * z 2 +
        d 2 * z 0 * z 1 + d 0 * d 1 * z 2 + d 0 * d 2 * z 1 +
        d 1 * d 2 * z 0,
    2 * d 1 * z 1,
    2 * d 2 * z 2
  ]

/-- R-5783.2: the exact mixed-difference coordinates and absorption of the
value `F(d)` by the span of all mixed differences. -/
def claim58495 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p →
    ∀ (d z : Fin 3 → ZMod p),
      mixedDifference p d z = mixedDifferenceFormula p d z ∧
        henonF p d ∈ mixedDifferenceSpan p d

def coordinateVector (p : ℕ) (i : Fin 3) : Fin 3 → ZMod p :=
  fun j => if j = i then 1 else 0

/-- R-5783.3: the case-wise absorption record used by the mixed-difference
proof.  Each listed coordinate direction is a concrete member of the same
span; the final conjunct retains the asserted absorption of `F(d)`. -/
def claim58497 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p →
    ∀ (d : Fin 3 → ZMod p),
      (∀ z : Fin 3 → ZMod p,
        mixedDifference p d z = mixedDifferenceFormula p d z) ∧
      (d 1 ≠ 0 → coordinateVector p 1 ∈ mixedDifferenceSpan p d) ∧
      (d 2 ≠ 0 → coordinateVector p 2 ∈ mixedDifferenceSpan p d) ∧
      (d 0 ≠ 0 → coordinateVector p 0 ∈ mixedDifferenceSpan p d) ∧
      (d 0 = 0 ∧ d 1 ≠ 0 ∧ d 2 = 0 →
        coordinateVector p 0 ∈ mixedDifferenceSpan p d) ∧
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 ≠ 0 →
        coordinateVector p 0 ∈ mixedDifferenceSpan p d) ∧
      (d 0 = 0 ∧ d 1 ≠ 0 ∧ d 2 ≠ 0 →
        coordinateVector p 0 ∈ mixedDifferenceSpan p d) ∧
      (d 0 ≠ 0 ∧ d 1 = 0 ∧ d 2 = 0 →
        coordinateVector p 0 ∈ mixedDifferenceSpan p d) ∧
      henonF p d ∈ mixedDifferenceSpan p d

end

end MathlibPlus.Open.ResearchFormalization.R5783
