import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.PrimeCyclotomic

/-- The trace-Chebyshev polynomials, defined by C₀ = 2, C₁ = X, and
Cₖ₊₂ = X Cₖ₊₁ - Cₖ. -/
def traceChebyshev (n : ℕ) : Polynomial ℤ :=
  (Nat.rec (motive := fun _ => Polynomial ℤ × Polynomial ℤ)
    (2, Polynomial.X)
    (fun _ ab => (ab.2, Polynomial.X * ab.2 - ab.1)) n).1

/-- The explicit prime-cyclotomic trace polynomial. -/
def primeTracePolynomial (p : ℕ) : Polynomial ℤ :=
  1 + (∑ k ∈ Finset.Icc 1 ((p - 1) / 2), traceChebyshev k)

/-- The reciprocal identity used to define the trace polynomial. -/
def reciprocalTraceIdentity (p : ℕ) (q : Polynomial ℤ) : Prop :=
  ∀ x : ℂ, x ≠ 0 →
    Polynomial.eval₂ (Int.castRingHom ℂ) x (Polynomial.cyclotomic p ℤ) =
      x ^ ((p - 1) / 2) *
        Polynomial.eval₂ (Int.castRingHom ℂ) (x + x⁻¹) q

/-- Unbounded-degree cyclotomic witnesses with interval roots, arithmetic
obstructions, and Mahler measure one. -/
def unbounded_degree_cyclotomic_witness : Prop :=
  (∀ B : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧
    B < (primeTracePolynomial p).natDegree) ∧
    ∀ p : ℕ, Nat.Prime p → p % 2 = 1 →
      let n := (p - 1) / 2
      Polynomial.Monic (primeTracePolynomial p) ∧
        (primeTracePolynomial p).natDegree = n ∧
        reciprocalTraceIdentity p (primeTracePolynomial p) ∧
        (∀ q : Polynomial ℤ, Polynomial.Monic q →
          reciprocalTraceIdentity p q → q = primeTracePolynomial p) ∧
        (∀ z : ℂ,
          Polynomial.eval₂ (Int.castRingHom ℂ) z (primeTracePolynomial p) = 0 →
            z.im = 0 ∧ (-2 : ℝ) ≤ z.re ∧ z.re ≤ (2 : ℝ)) ∧
        Polynomial.eval (2 : ℤ) (primeTracePolynomial p) = (p : ℤ) ∧
        Polynomial.eval (-2 : ℤ) (primeTracePolynomial p) = (-1 : ℤ) ^ n ∧
        Polynomial.discr (primeTracePolynomial p) ≠ 0 ∧
        Int.natAbs (Polynomial.discr (primeTracePolynomial p)) =
          p ^ ((p - 3) / 2) ∧
        Polynomial.mahlerMeasure (Polynomial.cyclotomic p ℂ) = 1

end MathlibPlus.Open.PrimeCyclotomic
