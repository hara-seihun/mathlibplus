import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.PolynomialBounds

open scoped BigOperators
noncomputable section

/-- The coefficient `ell^1` norm used by the polynomial bounds. -/
def polynomialL1 (p : Polynomial ℝ) : ℝ :=
  ∑ n ∈ p.support, |p.coeff n|

def coefficientRootEnvelope (p : Polynomial ℝ) : ℝ :=
  Finset.fold max 1
    (fun n : ℕ => if n = 0 then 1 else |p.coeff n| ^ ((1 : ℝ) / (n : ℝ)))
    (Finset.range (p.natDegree + 1))

def polynomialWithCoefficients (d : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  Polynomial.C 1 +
    ∑ n ∈ Finset.Icc 1 d, Polynomial.C (a n) * Polynomial.X ^ n

def coefficientEnvelopeFor (d : ℕ) (a : ℕ → ℝ) : ℝ :=
  Finset.fold max 1
    (fun n : ℕ => if n = 0 then 1 else |a n| ^ ((1 : ℝ) / (n : ℝ)))
    (Finset.range (d + 1))

/-- Claim 3064: the coefficient-root envelope is the displayed finite maximum. -/
def claim3064 : Prop :=
  ∀ (d : ℕ) (a : ℕ → ℝ),
    coefficientRootEnvelope (polynomialWithCoefficients d a) =
      coefficientEnvelopeFor d a

/-- Claim 3065: the coefficient `ell^1` product bound for bounded witness roots. -/
def claim3065 : Prop :=
  ∀ (N : ℕ) (S : Polynomial ℝ) (ρ : Fin N → ℝ) (R A : ℝ),
    (∀ j : Fin N, |ρ j| ≤ R) →
    polynomialL1 S ≤ A ^ (N + S.natDegree) →
    let D := N + S.natDegree
    let W := S * ∏ j : Fin N, (Polynomial.X - Polynomial.C (ρ j))
    polynomialL1 W ≤ polynomialL1 S * ∏ j : Fin N, (1 + |ρ j|) ∧
      polynomialL1 S * ∏ j : Fin N, (1 + |ρ j|) ≤
        (A * (1 + R)) ^ D ∧
      ∀ n : ℕ, |W.coeff n| ≤ (A * (1 + R)) ^ D

def chebyshevPair : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (1, Polynomial.X)
  | n + 1 =>
      ((chebyshevPair n).2,
        2 * Polynomial.X * (chebyshevPair n).2 - (chebyshevPair n).1)

def chebyshev (n : ℕ) : Polynomial ℝ := (chebyshevPair n).1

def affineArgument (c r : ℝ) : Polynomial ℝ :=
  (1 / r) • (Polynomial.X - Polynomial.C c)

def chebyshevH (c r : ℝ) : ℝ :=
  2 * (1 + |c|) / |r| + 1

def chebyshevExpansion (M : ℕ) (b : ℕ → ℝ) (c r : ℝ) : Polynomial ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    Polynomial.C (b m) * (chebyshev m).comp (affineArgument c r)

/-- Claim 3069: affine Chebyshev conversion and the resulting exponential norm bound. -/
def claim3069 : Prop :=
  (∀ (m : ℕ) (c r : ℝ), r ≠ 0 →
    polynomialL1 ((chebyshev m).comp (affineArgument c r)) ≤ chebyshevH c r ^ m) ∧
    (∀ (M D : ℕ) (b : ℕ → ℝ) (E c r : ℝ),
      M ≤ D → r ≠ 0 →
      (∀ m : ℕ, m ≤ M → |b m| ≤ E ^ D) →
      let S := chebyshevExpansion M b c r
      let H := chebyshevH c r
      polynomialL1 S ≤ ((M + 1 : ℕ) : ℝ) * E ^ D * H ^ M ∧
        polynomialL1 S ≤ (2 * E * H) ^ D)

def offsetPolynomial (r : ℝ) (q : ℕ → ℕ) (N : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ q N * (Polynomial.X - Polynomial.C r) ^ N

/-- Claim 3071: sublinear exponent offsets force an unbounded coefficient-root envelope. -/
def claim3071 : Prop :=
  ∀ (r : ℝ) (q : ℕ → ℕ),
    1 < r →
    (∀ N : ℕ, 0 < q N) →
    Filter.Tendsto (fun N : ℕ => (q N : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) →
    let Δ := offsetPolynomial r q
    (∀ N : ℕ,
      (Δ N).coeff (q N) = (-r) ^ N ∧
        Real.rpow r ((N : ℝ) / (q N : ℝ)) ≤
          coefficientRootEnvelope (1 + Δ N)) ∧
      Filter.Tendsto (fun N : ℕ => coefficientRootEnvelope (1 + Δ N))
        Filter.atTop Filter.atTop

end
end MathlibPlus.Open.ResearchFormalization.PolynomialBounds
