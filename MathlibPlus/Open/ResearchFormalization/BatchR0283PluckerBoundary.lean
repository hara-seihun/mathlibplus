import Mathlib

open scoped BigOperators
open Set

namespace MathlibPlus.Open.ResearchFormalization.BatchR0283

noncomputable section

/-- A rank-`r` maximal-minor index with its columns in increasing order. -/
abbrev OrderedMaximalMinorIndex (r n : ℕ) :=
  {M : Fin r ↪ Fin n // StrictMono M}

/-- The maximal Pluecker coordinate on the ordered-index carrier. -/
def pluckerMinor {r n : ℕ}
    (V : Matrix (Fin r) (Fin n) ℝ)
    (M : OrderedMaximalMinorIndex r n) : ℝ :=
  Matrix.det (V.submatrix id M.1)

/-- Scale exactly the columns outside an ordered maximal-minor index. -/
def torusScale {r n : ℕ}
    (M₀ : OrderedMaximalMinorIndex r n) (ε : ℝ)
    (V : Matrix (Fin r) (Fin n) ℝ) : Matrix (Fin r) (Fin n) ℝ :=
  fun i j => if j ∈ Set.range M₀.1 then V i j else ε * V i j

/-- The number of selected columns outside the fixed ordered index. -/
def outsideColumnCount {r n : ℕ}
    (M₀ M : OrderedMaximalMinorIndex r n) : ℕ :=
  (Finset.univ.filter (fun i : Fin r => M.1 i ∉ Set.range M₀.1)).card

/-- A finite linear functional in the ordered maximal Pluecker coordinates. -/
def linearPluckerFunctional {r n : ℕ}
    (a : OrderedMaximalMinorIndex r n → ℝ)
    (V : Matrix (Fin r) (Fin n) ℝ) : ℝ :=
  ∑ M : OrderedMaximalMinorIndex r n, a M * pluckerMinor V M

/-- The positive-Grassmannian matrix carrier used by both claims. -/
def strictlyTotallyPositive {r n : ℕ}
    (V : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  ∀ M : OrderedMaximalMinorIndex r n, 0 < pluckerMinor V M

/-- A subtraction-free linear Pluecker expression has no negative coefficient. -/
def subtractionFreeLinearPluckerForm {r n : ℕ}
    (a : OrderedMaximalMinorIndex r n → ℝ) : Prop :=
  ∀ M : OrderedMaximalMinorIndex r n, 0 ≤ a M

/-- Nonnegativity on the full strictly positive matrix/minor carrier. -/
def globallyNonnegativeLinearPluckerFunctional {r n : ℕ}
    (a : OrderedMaximalMinorIndex r n → ℝ) : Prop :=
  ∀ V : Matrix (Fin r) (Fin n) ℝ,
    strictlyTotallyPositive V →
      0 ≤ linearPluckerFunctional a V

/-- Claim 19438: ordered rank-`r` indices make every distinct index acquire a
positive outside-column power, and the finite functional has the stated
one-sided boundary limit. -/
def boundaryLimitIsolatesPluckerCoefficient_claim19438 : Prop :=
  ∀ (r n : ℕ)
    (V : Matrix (Fin r) (Fin n) ℝ)
    (a : OrderedMaximalMinorIndex r n → ℝ)
    (M₀ : OrderedMaximalMinorIndex r n),
    (∀ (ε : ℝ) (M : OrderedMaximalMinorIndex r n),
      pluckerMinor (torusScale M₀ ε V) M =
        ε ^ outsideColumnCount M₀ M * pluckerMinor V M) ∧
    (∀ ε : ℝ,
      pluckerMinor (torusScale M₀ ε V) M₀ = pluckerMinor V M₀) ∧
    (∀ M : OrderedMaximalMinorIndex r n, M ≠ M₀ →
      0 < outsideColumnCount M₀ M) ∧
    Filter.Tendsto
      (fun ε : ℝ => linearPluckerFunctional a (torusScale M₀ ε V))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (pluckerMinor V M₀ * a M₀))

/-- Claim 19439: a negative ordered Pluecker coefficient makes the same
positive-Grassmannian boundary degeneration negative near zero, ruling out
both global nonnegativity and a subtraction-free coefficient form. -/
def negativePluckerCoefficientForcesGrassmannianNegativity_claim19439 : Prop :=
  ∀ (r n : ℕ)
    (V : Matrix (Fin r) (Fin n) ℝ)
    (a : OrderedMaximalMinorIndex r n → ℝ)
    (M₀ : OrderedMaximalMinorIndex r n),
    strictlyTotallyPositive V →
    a M₀ < 0 →
      (∃ δ : ℝ, 0 < δ ∧
        ∀ ε : ℝ, 0 < ε → ε < δ →
          linearPluckerFunctional a (torusScale M₀ ε V) < 0) ∧
      ¬ globallyNonnegativeLinearPluckerFunctional a ∧
      ¬ subtractionFreeLinearPluckerForm a

end

end MathlibPlus.Open.ResearchFormalization.BatchR0283
