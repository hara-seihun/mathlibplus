import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchR1871

abbrev F2Vec (n : ℕ) := Fin n → ZMod 2

def basisVector {n : ℕ} (j : Fin n) : F2Vec n :=
  fun k => if k = j then 1 else 0

def zeroCoordinateSlice {n : ℕ} (i j : Fin n) : Type :=
  {x : F2Vec n // x i = 0 ∧ x j = 0}

noncomputable instance coordinateSliceFintype {n : ℕ} (i j : Fin n) :
    Fintype (zeroCoordinateSlice i j) := by
  classical
  let s : Finset (F2Vec n) :=
    Finset.univ.filter (fun x => x i = 0 ∧ x j = 0)
  exact Fintype.subtype s (by simp [s, zeroCoordinateSlice])

def bitToReal (b : Fin 2) : ℝ := b.val

noncomputable def uniformFiniteExpectation
    {α : Type} [Fintype α] (g : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x : α, g x

/-- The literal coordinate-transposition defect, before quotienting,
averaging, or projecting to a Cayley connection set. -/
noncomputable def literalTranspositionDefect
    (n : ℕ)
    (f : Fin n → F2Vec n → Fin 2)
    (i j : Fin n) (h : i ≠ j) : ℝ :=
  (1 / 2 : ℝ) *
    uniformFiniteExpectation
      (fun x : zeroCoordinateSlice i j =>
        |bitToReal (f i x.1) - bitToReal (f j x.1)| +
        |bitToReal (f i (x.1 + basisVector j)) -
          bitToReal (f j (x.1 + basisVector i))|)

end MathlibPlus.Open.Research.FormalizationBatchR1871
