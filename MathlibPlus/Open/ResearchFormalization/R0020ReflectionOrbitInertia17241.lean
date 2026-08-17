import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0020ReflectionOrbitInertia17241

noncomputable section

/-- The finite occurrence-space reflection form. -/
def reflectionForm {Z : Type*} [Fintype Z]
    (τ : Z → Z) (v w : Z → ℂ) : ℂ :=
  ∑ ρ : Z, v ρ * star (w (τ ρ))

def reflectionNondegenerate {Z : Type*} [Fintype Z]
    (τ : Z → Z) : Prop :=
  ∀ v : Z → ℂ,
    (∀ w : Z → ℂ, reflectionForm τ v w = 0) → v = 0

def reflectionPositiveSemidefinite {Z : Type*} [Fintype Z]
    (τ : Z → Z) : Prop :=
  ∀ v : Z → ℂ, 0 ≤ (reflectionForm τ v v).re

/-- A fixed-occurrence coordinate vector. -/
def fixedBasis {Z : Type*} [Fintype Z]
    (ρ : Z) (a : ℂ) : Z → ℂ :=
  fun z => if z = ρ then a else 0

/-- The explicit negative vector on a nontrivial two-cycle. -/
def twoCycleVector {Z : Type*} [Fintype Z]
    (τ : Z → Z) (ρ : Z) : Z → ℂ :=
  fun z => if z = ρ then 1 else if z = τ ρ then -1 else 0

abbrev SignatureCoordinates (r p : ℕ) :=
  (Fin r → ℂ) × (Fin p → ℂ) × (Fin p → ℂ)

def diagonalSignatureForm (r p : ℕ)
    (v w : SignatureCoordinates r p) : ℂ :=
  (∑ i : Fin r, v.1 i * star (w.1 i)) +
    (∑ i : Fin p, v.2.1 i * star (w.2.1 i)) -
      ∑ i : Fin p, v.2.2 i * star (w.2.2 i)

/-- Congruence to the explicit `(+1,+1,-1)` signature coordinates. -/
def hasReflectionSignature {Z : Type*} [Fintype Z]
    (τ : Z → Z) (r p : ℕ) : Prop :=
  ∃ e : (Z → ℂ) ≃ₗ[ℂ] SignatureCoordinates r p,
    ∀ v w : SignatureCoordinates r p,
      reflectionForm τ (e.symm v) (e.symm w) =
        diagonalSignatureForm r p v w

/-- Claim 17241: a fixed-point occurrence gives the one-dimensional `[1]`
block and a strictly positive quadratic value on every nonzero vector. -/
def claim17241 : Prop :=
  ∀ {Z : Type*} [Fintype Z]
    (τ : Z → Z) (ρ : Z),
    Function.Involutive τ →
      τ ρ = ρ →
        (∀ a b : ℂ,
          reflectionForm τ (fixedBasis ρ a) (fixedBasis ρ b) =
            a * star b) ∧
        (∀ a : ℂ, a ≠ 0 →
          0 < (reflectionForm τ (fixedBasis ρ a) (fixedBasis ρ a)).re)

/-- Claim 17243: an involution with `r` fixed occurrences and `p` two-cycles
has the exact nondegenerate signature `(r+p,p,0)` and occurrence count
`r+2p`. -/
def claim17243 : Prop :=
  ∀ {Z : Type*} [Fintype Z]
    (τ : Z → Z),
    Function.Involutive τ →
      let r := Fintype.card {ρ : Z // τ ρ = ρ}
      ∃ p : ℕ,
        Fintype.card Z = r + 2 * p ∧
          reflectionNondegenerate τ ∧
            hasReflectionSignature τ (r + p) p

/-- Claim 17244: the finite reflection form is positive semidefinite exactly
when every occurrence is fixed, and every nontrivial two-cycle supplies the
explicit supported negative vector. -/
def claim17244 : Prop :=
  ∀ {Z : Type*} [Fintype Z]
    (τ : Z → Z),
    Function.Involutive τ →
      (reflectionPositiveSemidefinite τ ↔
        ∀ ρ : Z, τ ρ = ρ) ∧
      (∀ ρ : Z, τ ρ ≠ ρ →
        (twoCycleVector τ ρ) ρ = 1 ∧
          (twoCycleVector τ ρ) (τ ρ) = -1 ∧
          (∀ z : Z,
            z ≠ ρ → z ≠ τ ρ → twoCycleVector τ ρ z = 0) ∧
          (reflectionForm τ (twoCycleVector τ ρ)
              (twoCycleVector τ ρ)).re < 0)

end

end MathlibPlus.Open.ResearchFormalization.R0020ReflectionOrbitInertia17241
