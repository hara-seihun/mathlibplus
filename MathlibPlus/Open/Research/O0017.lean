import Mathlib

namespace MathlibPlus.Open.Research.O0017

open scoped BigOperators

noncomputable section

/-- The orientation-only signed enumerator of a finite graded face set. -/
def signedFaceEnumerator {α : Type*} (F : Finset α) (rk : α → ℕ)
    (ε : α → ℤ) (hε : ∀ f ∈ F, ε f = -1 ∨ ε f = 1) : Polynomial ℤ :=
  ∑ f ∈ F, Polynomial.C (ε f) * Polynomial.X ^ rk f

/-- A weighted enumerator for singleton cells indexed by their ranks. -/
def weightedFaceEnumeratorReal (F : Finset ℕ) (w : ℕ → ℝ)
    (ε : ℕ → ℤ) : Polynomial ℝ :=
  ∑ j ∈ F, Polynomial.C (w j * (ε j : ℝ)) * Polynomial.X ^ j

/-- The rational version of the weighted singleton enumerator. -/
def weightedFaceEnumeratorRat (F : Finset ℕ) (w : ℕ → ℚ)
    (ε : ℕ → ℤ) : Polynomial ℚ :=
  ∑ j ∈ F, Polynomial.C (w j * (ε j : ℚ)) * Polynomial.X ^ j

/-- Every polynomial is realized by one weighted singleton for each nonzero term,
with the stated absolute-value weights and coefficient signs, over both fields. -/
def claim9585 : Prop :=
  (∀ P : Polynomial ℝ,
    weightedFaceEnumeratorReal P.support
        (fun j => |P.coeff j|)
        (fun j => if P.coeff j < 0 then (-1 : ℤ) else 1) = P) ∧
  (∀ P : Polynomial ℚ,
    weightedFaceEnumeratorRat P.support
        (fun j => |P.coeff j|)
        (fun j => if P.coeff j < 0 then (-1 : ℤ) else 1) = P)

end

end MathlibPlus.Open.Research.O0017
