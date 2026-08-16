import Mathlib

namespace MathlibPlus.Open.Algebra.Claim12520

noncomputable def n4Polynomial : Polynomial ℝ :=
  (1 : Polynomial ℝ) + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3

noncomputable def coefficient (q : ℤ) : ℝ :=
  if h : 0 ≤ q then (n4Polynomial).coeff q.toNat else 0

noncomputable def rectangularMinor (r k : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    coefficient ((k : ℤ) + (j.val : ℤ) - (i.val : ℤ)))

noncomputable def fullToeplitzMinor (rows cols : Finset ℕ)
    (h : rows.card = cols.card) : ℝ :=
  Matrix.det (fun i j : Fin rows.card =>
    coefficient
      (((cols.orderEmbOfFin h.symm j : ℕ) : ℤ) -
        ((rows.orderEmbOfFin rfl i : ℕ) : ℤ)))

def allFiniteToeplitzMinorsNonnegative : Prop :=
  ∀ (rows cols : Finset ℕ) (h : rows.card = cols.card),
    0 ≤ fullToeplitzMinor rows cols h

def rectangularMinorsNonnegativeAtFour : Prop :=
  ∀ r k : ℕ, 1 ≤ r → 1 ≤ k → 0 ≤ rectangularMinor r k

def rowIndex : Fin 3 → ℕ := ![0, 1, 2]

def columnIndex : Fin 3 → ℕ := ![1, 2, 4]

noncomputable def coefficientWitness : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => coefficient (((columnIndex j : ℕ) : ℤ) - ((rowIndex i : ℕ) : ℤ))

def displayedWitness : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 0; 1, 1, 1; 0, 1, 1]

def noncontiguousMinorsRetainInformation : Prop :=
  rectangularMinorsNonnegativeAtFour ∧
  coefficientWitness = displayedWitness ∧
  Matrix.det coefficientWitness = -1 ∧
  ¬ allFiniteToeplitzMinorsNonnegative

end MathlibPlus.Open.Algebra.Claim12520
