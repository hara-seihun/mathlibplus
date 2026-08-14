import Mathlib

namespace MathlibPlus.Ingest.R3186

open scoped BigOperators
noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Coefficients of the finite squarefree algebra on `E`.

The value at `S` is the coefficient of the squarefree monomial whose support is
`S`; multiplication is the convolution restricted to disjoint supports. -/
abbrev SquarefreeSeries (E : Type*) := Finset E → ℚ

def squarefreeOne : SquarefreeSeries E :=
  fun S => if S = ∅ then 1 else 0

def squarefreeMul (f g : SquarefreeSeries E) : SquarefreeSeries E :=
  fun S =>
    ∑ A ∈ (Finset.univ : Finset (Finset E)),
      ∑ B ∈ (Finset.univ : Finset (Finset E)),
        if Disjoint A B ∧ A ∪ B = S then f A * g B else 0

def squarefreeZ (K : Finset E → ℚ) : SquarefreeSeries E :=
  fun S => if S.Nonempty then K S else 1

def squarefreeZMinusOne (K : Finset E → ℚ) : SquarefreeSeries E :=
  fun S => squarefreeZ K S - squarefreeOne S

def squarefreePow (f : SquarefreeSeries E) : ℕ → SquarefreeSeries E
  | 0 => squarefreeOne
  | n + 1 => squarefreeMul (squarefreePow f n) f

/-- The finite formal logarithm in the squarefree quotient.  The augmentation
ideal is nilpotent of degree `Fintype.card E + 1`, so these are all terms. -/
def squarefreeLog (K : Finset E → ℚ) : SquarefreeSeries E :=
  fun S =>
    ∑ n ∈ Finset.range (Fintype.card E),
      ((-1 : ℚ) ^ (n + 2) / ((n + 1 : ℕ) : ℚ)) *
        squarefreePow (squarefreeZMinusOne K) (n + 1) S

def isSetPartition (S : Finset E) (π : Finset (Finset E)) : Prop :=
  (∀ B ∈ π, B.Nonempty ∧ B ⊆ S) ∧
    (∀ ⦃B C⦄, B ∈ π → C ∈ π → B ≠ C → Disjoint B C) ∧
    S = π.biUnion (fun B => B)

def mobiusKappa (K : Finset E → ℚ) (S : Finset E) : ℚ := by
  classical
  exact
    ∑ π ∈ (Finset.univ : Finset (Finset (Finset E))).filter
        (isSetPartition S),
      (-1 : ℚ) ^ (π.card - 1) *
        ((π.card - 1).factorial : ℚ) *
        ∏ B ∈ π, K B

/-- The coefficient identity for the logarithm of the concrete squarefree
partition function `squarefreeZ K`. -/
def squarefreeLogMobiusClaim (K : Finset E → ℚ) : Prop :=
  ∀ S, S.Nonempty → squarefreeLog K S = mobiusKappa K S

section RankFour

/-- The moment sequence in the rank-four witness. -/
def rankFourMoment (a b : ℝ) (q : ℕ) : ℝ :=
  1 + a * Real.sqrt 3 / (4 : ℝ) ^ q + b * Real.sqrt 2 / (9 : ℝ) ^ q

/-- The completed moments used as the Bezout-matrix entries. -/
def rankFourH (a b : ℝ) (q : ℕ) : ℝ :=
  rankFourMoment a b q / (Nat.factorial (2 * q) : ℝ)

def rankFourEntry (a b : ℝ) (i j : Fin 4) : ℝ :=
  ∑ q ∈ Finset.range (min i.val j.val + 1),
    ((i.val + j.val + 1 - 2 * q : ℕ) : ℝ) *
      rankFourH a b q *
      rankFourH a b (i.val + j.val + 1 - q)

def rankFourMatrix (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => rankFourEntry a b i j

def rankFourDeterminant (a b : ℝ) : ℝ :=
  Matrix.det (rankFourMatrix a b)

def rankFourNormalizedDeterminant (a b : ℝ) : ℝ :=
  rankFourDeterminant a b / rankFourDeterminant 0 0

/-- The actual iterated partial derivative of the logarithm of the normalized
rank-four determinant, evaluated at the origin. -/
def rankFourMixedLogDerivative : ℝ :=
  deriv
    (fun a : ℝ =>
      deriv (fun b : ℝ => Real.log (rankFourNormalizedDeterminant a b)) 0)
    0

/-- Exact rank-four negative connected pair, including the common-scale
consequence stated in the claim. -/
def rankFourNegativePair : Prop :=
  let value : ℝ :=
    -(35948224158017 : ℝ) / 26748301344768 * Real.sqrt 6
  rankFourMixedLogDerivative = value ∧
    rankFourMixedLogDerivative < 0 ∧
    rankFourMixedLogDerivative / 6 = value / 6 ∧
    rankFourMixedLogDerivative / 6 < 0

end RankFour

end
end MathlibPlus.Ingest.R3186
