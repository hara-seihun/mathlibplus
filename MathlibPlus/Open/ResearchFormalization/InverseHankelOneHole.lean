import Mathlib

noncomputable section
universe u

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! Gaussian-node moment and residue data from the repair context of Claim 7175. -/
def nodeMoment (n : ℕ) (x w : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin n, w j * (x j) ^ k

def momentMatrix (n : ℕ) (x w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => nodeMoment n x w (a.val + b.val)

def nodePolynomial (n : ℕ) (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (Polynomial.X - Polynomial.C (x j))

def reciprocalNodePolynomial (n : ℕ) (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (Polynomial.C 1 - Polynomial.C (x j) * Polynomial.X)

def vectorPolynomial (n : ℕ) (v : Fin n → ℝ) : Polynomial ℝ :=
  ∑ k : Fin n, Polynomial.C (v k) * Polynomial.X ^ k.val

def truncateBelow (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  Finset.sum (Finset.range n) (fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k)

def truncatedResiduePolynomial (n : ℕ) (x v : Fin n → ℝ) : Polynomial ℝ :=
  truncateBelow n (reciprocalNodePolynomial n x * vectorPolynomial n v)

def residueObservable (n : ℕ) (x w v : Fin n → ℝ) (j : Fin n) : ℝ :=
  x j ^ (n - 1) *
    Polynomial.eval (1 / x j)
      (truncatedResiduePolynomial n x v)

def dualResidueWeight (n : ℕ) (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  1 /
    (w j *
      (Polynomial.eval (x j) (Polynomial.derivative (nodePolynomial n x))) ^ 2)

def inverseHankelQuadratic (n : ℕ) (x w v : Fin n → ℝ) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n,
    v a * ((momentMatrix n x w)⁻¹ a b) * v b

def finiteExpectation (ν : Fin n → ℝ) (f : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, ν j * f j

/-- The inverse-Hankel energy is the one-hole expectation (Claim 7175). -/
def inverseHankelEnergyAsOneHoleExpectation : Prop :=
  ∀ (n : ℕ) (x w v : Fin n → ℝ)
    (P : Polynomial ℝ) (h : ℝ) (ν : Fin n → ℝ),
    0 < n →
    (∀ j : Fin n, 0 < x j) →
    (∀ i j : Fin n, i.val < j.val → x i < x j) →
    (∀ j : Fin n, 0 < w j) →
    P.Monic →
    P.natDegree = n - 1 →
    (∀ Q : Polynomial ℝ, Q.natDegree < n - 1 →
      (∑ j : Fin n,
        w j * Polynomial.eval (x j) P * Polynomial.eval (x j) Q) = 0) →
    h = ∑ j : Fin n, w j * (Polynomial.eval (x j) P) ^ 2 →
    (∀ j : Fin n, 0 ≤ ν j) →
    (∑ j : Fin n, ν j = 1) →
    (∀ j : Fin n, ν j = h * dualResidueWeight n x w j) →
    inverseHankelQuadratic n x w v =
      (1 / h) * finiteExpectation ν (fun j => (residueObservable n x w v j) ^ 2)

end MathlibPlus.Open.ResearchFormalizationBatch
