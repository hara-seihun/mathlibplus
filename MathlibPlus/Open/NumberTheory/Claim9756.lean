import MathlibPlus.Open.NumberTheory.Claim9763

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace MathlibPlus.Open.NumberTheory.Claim9756

/-- The divisor-whitening vector from the admitted transform. -/
def divisorWhiteningVector {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : ℕ → H) (n : ℕ) : H :=
  Finset.sum n.divisors (fun d =>
    (((d : ℝ) / (n : ℝ)) *
      (ArithmeticFunction.moebius (n / d) : ℝ)) • e d)

/-- The arithmetic whitening weight `R(n)`. -/
def arithmeticWhiteningWeight (n : ℕ) : ℝ :=
  Finset.prod n.primeFactors (fun p => 1 - ((p : ℝ)⁻¹) ^ 2)

/-- The finite prime tensor form of the gcd kernel. -/
def primeExponent (n p : ℕ) : ℕ :=
  n.factorization p

def primeTensorSupport (d e : ℕ) : Finset ℕ :=
  (d.factorization.support ∪ e.factorization.support)

def primeTensorGcdKernel (d e : ℕ) : ℝ :=
  Finset.prod (primeTensorSupport d e) (fun p =>
    ((p : ℝ)⁻¹) ^ Nat.dist (primeExponent d p) (primeExponent e p))

/-- A local orthonormal innovation family. -/
def orthonormalInnovationFamily {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℕ → H) : Prop :=
  ∀ i j : ℕ, ⟪f i, f j⟫ = if i = j then 1 else 0

/-- The causal local prime AR(1) vector. -/
def localPrimeAR1Vector {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ℕ) (f : ℕ → H) (a : ℕ) : H :=
  let r : ℝ := (p : ℝ)⁻¹
  r ^ a • f 0 +
    Real.sqrt (1 - r ^ 2) •
      ∑ j ∈ Finset.Icc 1 a, r ^ (a - j) • f j

/-- Exact global divisor orthogonality, normalized coordinates, and the local
prime-AR(1) tensor description. -/
def claim9756 : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (e : ℕ → H),
    (∀ d f : ℕ, 0 < d → 0 < f →
      ⟪e d, e f⟫ =
        ((Nat.gcd d f : ℝ) ^ 2) / ((d : ℝ) * (f : ℝ))) →
    let z : ℕ → H := divisorWhiteningVector e
    let R : ℕ → ℝ := arithmeticWhiteningWeight
    (∀ d f : ℕ, 0 < d → 0 < f →
      ⟪e d, e f⟫ = primeTensorGcdKernel d f) ∧
    (∀ n : ℕ, 0 < n → 0 < R n) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      ⟪z m, z n⟫ = if m = n then R n else 0) ∧
    (∀ n : ℕ, 0 < n →
      e n =
        Finset.sum n.divisors (fun d =>
          ((d : ℝ) / (n : ℝ)) • z d)) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      ⟪(Real.sqrt (R m))⁻¹ • z m,
        (Real.sqrt (R n))⁻¹ • z n⟫ = if m = n then 1 else 0) ∧
    (∀ p : ℕ, p.Prime →
      ∀ f : ℕ → H, orthonormalInnovationFamily f →
        ∀ a b : ℕ,
          ⟪localPrimeAR1Vector p f a,
            localPrimeAR1Vector p f b⟫ =
            ((p : ℝ)⁻¹) ^ Nat.dist a b)

end MathlibPlus.Open.NumberTheory.Claim9756
