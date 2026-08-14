import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.K0033

open Matrix

abbrev Three := Fin 3

/-- The diagonal signature of a real diagonal three-dimensional form. -/
def diagonalSignature (a b c : ℝ) : ℕ × ℕ × ℕ :=
  ((if 0 < a then 1 else 0) + (if 0 < b then 1 else 0) + (if 0 < c then 1 else 0),
   (if a < 0 then 1 else 0) + (if b < 0 then 1 else 0) + (if c < 0 then 1 else 0),
   (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) + (if c = 0 then 1 else 0))

def scalarChannel (x : ℝ) : Matrix Three Three ℝ :=
  Matrix.diagonal ![1 + x / 2, -1, -x / 2]

def rootMatrix : Matrix Three Three ℝ :=
  !![1, 3, 0; 3, 1, 0; 0, 0, 1]

def arthurMatrix : Matrix Three Three ℝ :=
  Matrix.diagonal ![1, 3, -4]

def nonsingularCongruence (A B : Matrix Three Three ℝ) : Prop :=
  ¬ ∃ P : Matrix Three Three ℝ, P.det ≠ 0 ∧ P.transpose * A * P = B

def signatureMatrix3 (p : ℕ) : Matrix Three Three ℝ :=
  Matrix.diagonal (fun i => if i.val < p then 1 else -1)

def hasInertia3 (M : Matrix Three Three ℝ) (p q : ℕ) : Prop :=
  p + q = 3 ∧ ∃ P : Matrix Three Three ℝ,
    P.det ≠ 0 ∧ P.transpose * M * P = signatureMatrix3 p

def claim7755 : Prop :=
  (∀ x : ℝ, 0 < x → x ≤ 1 →
    diagonalSignature (1 + x / 2) (-1) (-x / 2) = (1, 2, 0) ∧
    hasInertia3 (scalarChannel x) 1 2) ∧
  hasInertia3 rootMatrix 2 1 ∧
  hasInertia3 arthurMatrix 2 1 ∧
  (∃ v : Three → ℝ, v ≠ 0 ∧ scalarChannel 0 *ᵥ v = 0) ∧
  (∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    nonsingularCongruence (scalarChannel x) rootMatrix ∧
    nonsingularCongruence (scalarChannel x) arthurMatrix)

end MathlibPlus.Open.Research.K0033
