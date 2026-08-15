import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

abbrev PrimeIndex (n : ℕ) := {p // p ∈ n.primeFactors}

def primeExponent (n : ℕ) (p : PrimeIndex n) : ℕ := n.factorization p.1

abbrev TensorBasisIndex (n : ℕ) :=
  ∀ p : PrimeIndex n, Fin (primeExponent n p + 1)

def complementCoordinate {m : ℕ} (i : Fin (m + 1)) : Fin (m + 1) :=
  ⟨m - i.1, by omega⟩

def tensorComplement (n : ℕ) (i : TensorBasisIndex n) : TensorBasisIndex n :=
  fun p => complementCoordinate (i p)

def primeLocalInteger (n : ℕ) (p : PrimeIndex n)
    (i : TensorBasisIndex n) : ℤ :=
  (primeExponent n p : ℤ) - 2 * (i p).1

def tensorEigenvalue (n : ℕ) (i : TensorBasisIndex n) : ℂ :=
  ∑ p : PrimeIndex n,
    (Real.log (p.1 : ℝ) : ℂ) * (primeLocalInteger n p i : ℂ)

def globalCartan (n : ℕ) : Matrix (TensorBasisIndex n) (TensorBasisIndex n) ℂ :=
  fun i j => if i = j then tensorEigenvalue n i else 0

def globalReversal (n : ℕ) : Matrix (TensorBasisIndex n) (TensorBasisIndex n) ℂ :=
  fun i j => if i = tensorComplement n j then 1 else 0

/-- One local tensor term in the displayed sum for `Y_n`. -/
def localSkewCurrentTerm (n : ℕ) (p : PrimeIndex n) :
    Matrix (TensorBasisIndex n) (TensorBasisIndex n) ℂ :=
  fun i j =>
    if i = tensorComplement n j then
      -(Real.log (p.1 : ℝ) : ℂ) * (primeLocalInteger n p j : ℂ)
    else 0

/-- The displayed sum of local `-J_k H_k` terms, on the tensor basis. -/
def globalSkewCurrent (n : ℕ) : Matrix (TensorBasisIndex n) (TensorBasisIndex n) ℂ :=
  ∑ p : PrimeIndex n, localSkewCurrentTerm n p

/-- Global anticommutation and the skew-current identity. -/
def claim_7128 : Prop :=
  ∀ n : ℕ, 1 < n →
    globalReversal n * globalCartan n =
        -(globalCartan n * globalReversal n) ∧
      globalSkewCurrent n = -(globalReversal n * globalCartan n)

/-- The log-prime eigenvalue of the global Cartan operator. -/
def claim_7130 : Prop :=
  ∀ n : ℕ, 1 < n →
    ∀ i : TensorBasisIndex n,
      globalCartan n i i = tensorEigenvalue n i

end
end MathlibPlus.Open.Research
