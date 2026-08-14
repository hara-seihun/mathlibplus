import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev TernaryVector (d : ℕ) := Fin d → ZMod 3

/-- Total degree of an exponent vector with the scout's representatives `0,1,2`. -/
def exponentDegree {m : ℕ} (e : Fin m → Fin 3) : ℕ :=
  ∑ i : Fin m, (e i).val

def oddPositiveExponent {m : ℕ} (e : Fin m → Fin 3) : Prop :=
  0 < exponentDegree e ∧ Odd (exponentDegree e)

/-- Evaluation of a coordinatewise ternary polynomial in the specified normal form. -/
def ternaryPolynomialEval {m n : ℕ}
    (coeff : (Fin m → Fin 3) → (Fin n → ZMod 3))
    (x : TernaryVector m) : TernaryVector n :=
  fun j =>
    ∑ e : Fin m → Fin 3,
      coeff e j * ∏ i : Fin m, x i ^ (e i).val

def oddTernaryPolynomialMap {m n : ℕ}
    (f : TernaryVector m → TernaryVector n) : Prop :=
  ∃ coeff : (Fin m → Fin 3) → (Fin n → ZMod 3),
    (∀ e, (∃ j, coeff e j ≠ 0) → oddPositiveExponent e) ∧
    (∀ x, f x = ternaryPolynomialEval coeff x)

/-- The triangular shear attached to a map `f`. -/
def triangularShear {m n : ℕ}
    (f : TernaryVector m → TernaryVector n) :
    TernaryVector m × TernaryVector n → TernaryVector m × TernaryVector n :=
  fun xz => (xz.1, xz.2 + f xz.1)

/-- Claim 42421: an odd-positive-degree ternary polynomial map is odd. -/
def oddTriangularShears : Prop :=
  ∀ (m n : ℕ) (f : TernaryVector m → TernaryVector n),
    oddTernaryPolynomialMap f →
    ∀ x, f (-x) = -f x

/-- The normalized derivative from Claim 42422. -/
def normalizedDerivative {m n : ℕ}
    (f : TernaryVector m → TernaryVector n)
    (a w : TernaryVector m) : TernaryVector n :=
  f (w + a) - f w

/-- The derivative-difference subspace `K_a`. -/
def derivativeSubspace {m n : ℕ}
    (f : TernaryVector m → TernaryVector n)
    (a : TernaryVector m) : Submodule (ZMod 3) (TernaryVector n) :=
  Submodule.span (ZMod 3)
    {v | ∃ w : TernaryVector m,
      v = normalizedDerivative f a w - normalizedDerivative f a 0}

def normalizedShadowCondition {m n : ℕ}
    (f : TernaryVector m → TernaryVector n)
    (shadow : TernaryVector m →ₗ[ZMod 3] TernaryVector n) : Prop :=
  ∀ ⦃a : TernaryVector m⦄, a ≠ 0 →
    shadow a - f a ∈ derivativeSubspace f a

def annihilatorShadowEquations {m n : ℕ}
    (f : TernaryVector m → TernaryVector n)
    (shadow : TernaryVector m →ₗ[ZMod 3] TernaryVector n) : Prop :=
  ∀ ⦃a : TernaryVector m⦄, a ≠ 0 →
    ∀ φ : TernaryVector n →ₗ[ZMod 3] ZMod 3,
      (∀ v ∈ derivativeSubspace f a, φ v = 0) →
      φ (shadow a) = φ (f a)

/-- Claim 42422: membership in every normalized derivative subspace is exactly
    the displayed annihilator linear system. -/
def normalizedDerivativeShadowEquivalence : Prop :=
  ∀ (m n : ℕ) (f : TernaryVector m → TernaryVector n)
    (shadow : TernaryVector m →ₗ[ZMod 3] TernaryVector n),
    normalizedShadowCondition f shadow ↔ annihilatorShadowEquations f shadow

end MathlibPlus.Open.ResearchFormalizationBatch
