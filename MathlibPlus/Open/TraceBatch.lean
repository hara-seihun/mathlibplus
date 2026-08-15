import Mathlib

namespace MathlibPlus.Open.TraceBatch

noncomputable section

abbrev TraceCoeff := MvPolynomial ℕ ℚ

def monomialWeight (m : ℕ →₀ ℕ) : ℕ :=
  Finset.sum m.support (fun n => (n + 1) * m n)

def weightedAt (p : Polynomial TraceCoeff) (w : ℕ) : Prop :=
  ∀ a ∈ p.support, ∀ m ∈ (p.coeff a).support,
    a + monomialWeight m = w

def monicWeightedTraceContext (C : Polynomial TraceCoeff) (c : ℕ) : Prop :=
  C.natDegree = c ∧ C.coeff c = 1 ∧ weightedAt C c

def rootClosure (p : Polynomial TraceCoeff) : TraceCoeff :=
  Finset.sum p.support (fun a => MvPolynomial.X (a + 1) * p.coeff a)

def shiftedRootClosure (s : ℕ) (p : Polynomial TraceCoeff) : TraceCoeff :=
  Finset.sum p.support (fun a => MvPolynomial.X (a + s) * p.coeff a)

def shiftTrace (C : Polynomial TraceCoeff) (j : ℕ) : TraceCoeff :=
  rootClosure (Polynomial.X ^ j * C)

def coefficientPolynomial (h : ℕ → TraceCoeff) (q : ℕ) : Polynomial TraceCoeff :=
  Finset.sum (Finset.range (q + 1))
    (fun a => Polynomial.C (h a) * Polynomial.X ^ a)

def linearWithCoefficient (n : ℕ) (a p : TraceCoeff) : Prop :=
  ∃ q : TraceCoeff, p = a * MvPolynomial.X n + q ∧ n ∉ q.vars

def monicLinearAt (n : ℕ) (p : TraceCoeff) : Prop :=
  linearWithCoefficient n 1 p

def priorIdeal (s : ℕ → TraceCoeff) (i : ℕ) : Ideal TraceCoeff :=
  Ideal.span (Set.range (fun j : {j : ℕ // j < i} => s j.1))

def regularPrefix (s : ℕ → TraceCoeff) (n : ℕ) : Prop :=
  ∀ i, i < n →
    IsRegular (Ideal.Quotient.mk (priorIdeal s i) (s i))

/-- Claim 6254. -/
def shiftedCommonContextTraceSequence : Prop :=
  ∀ (c : ℕ) (C : Polynomial TraceCoeff),
    monicWeightedTraceContext C c →
      ∀ j, 1 ≤ j →
        shiftTrace C j =
          Finset.sum (Finset.range (c + 1))
            (fun i => MvPolynomial.X (i + j) * C.coeff i)

/-- Claim 6255. -/
def privateVariableTriangularity : Prop :=
  ∀ (c : ℕ) (C : Polynomial TraceCoeff),
    monicWeightedTraceContext C c →
      ∀ j, 1 ≤ j →
        linearWithCoefficient (c + j) (C.coeff c) (shiftTrace C j) ∧
          (∀ k, 1 ≤ k → k < j →
            c + j ∉ (shiftTrace C k).vars) ∧
          C.coeff c = 1

/-- Claim 6256. -/
def shiftedTraceRegularity : Prop :=
  ∀ (c : ℕ) (C : Polynomial TraceCoeff),
    monicWeightedTraceContext C c →
      ∀ q, regularPrefix (fun j => shiftTrace C (j + 1)) (q + 1)

/-- Claim 6257. -/
def commonContextResidueExpansion : Prop :=
  ∀ (q : ℕ) (C : Polynomial TraceCoeff) (h : ℕ → TraceCoeff),
    rootClosure
        (Polynomial.X * C * coefficientPolynomial h q) =
      Finset.sum (Finset.range (q + 1))
        (fun a => h a * shiftTrace C (a + 1))

/-- Claim 6258. -/
def completeFirstKoszulClassification : Prop :=
  ∀ (q : ℕ) (C : Polynomial TraceCoeff),
    regularPrefix (fun j => shiftTrace C (j + 1)) (q + 1) →
      ∀ h : Fin (q + 1) → TraceCoeff,
        (∑ a : Fin (q + 1), h a * shiftTrace C (a.1 + 1) = 0) ↔
          ∃ g : Fin (q + 1) → Fin (q + 1) → TraceCoeff,
            (∀ a b, g a b = -g b a) ∧
              (∀ a,
                h a = ∑ b : Fin (q + 1),
                  shiftTrace C (b.1 + 1) * g a b)

/-- Claim 6260. -/
def principalLinearResidual : Prop :=
  ∀ (c : ℕ) (C : Polynomial TraceCoeff),
    monicWeightedTraceContext C c →
      ∀ h₀ h₁ : TraceCoeff,
        h₀ * shiftTrace C 1 + h₁ * shiftTrace C 2 = 0 →
          ∃ g : TraceCoeff,
            h₀ = shiftTrace C 2 * g ∧
              h₁ = -shiftTrace C 1 * g

/-- Claim 6294. -/
def shiftedRootForgettingMap : Prop :=
  ∀ s, 0 < s →
    ∀ (a : ℕ) (m : ℕ →₀ ℕ),
      shiftedRootClosure s
          (Polynomial.X ^ a * Polynomial.C (MvPolynomial.monomial m 1)) =
        MvPolynomial.X (a + s) * MvPolynomial.monomial m 1

/-- Claim 6304. -/
def rootClosureMap : Prop :=
  ∀ (a : ℕ) (m : ℕ →₀ ℕ),
    rootClosure
        (Polynomial.X ^ a * Polynomial.C (MvPolynomial.monomial m 1)) =
      MvPolynomial.X (a + 1) * MvPolynomial.monomial m 1

end

end MathlibPlus.Open.TraceBatch
