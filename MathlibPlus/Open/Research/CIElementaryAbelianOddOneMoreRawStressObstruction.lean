import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.Research.CIElementaryAbelianOddOneMoreRawStressObstruction

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

abbrev PrimeField (p : ℕ) := ZMod p
abbrev PrimeFieldStar (p : ℕ) := {x : PrimeField p // x ≠ 0}
abbrev RetainedPoint (p : ℕ) (Z : Finset (PrimeFieldStar p)) :=
  {x : PrimeFieldStar p // x ∉ Z}
abbrev RetainedTriple (p : ℕ) (Z : Finset (PrimeFieldStar p)) :=
  {τ : Finset (RetainedPoint p Z) //
    τ.card = 3 ∧ Finset.sum τ (fun x : RetainedPoint p Z => (x.1.1 : PrimeField p)) = 0}
abbrev TripleOrientation {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) :=
  {o : Fin 3 → RetainedPoint p Z //
    Function.Injective o ∧
      (∀ i : Fin 3, o i ∈ τ.1) ∧
      (∀ x : RetainedPoint p Z, x ∈ τ.1 ↔ ∃ i : Fin 3, o i = x)}

def retainedValue {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (x : RetainedPoint p Z) : PrimeField p :=
  x.1.1

def tripleA {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  retainedValue (o.1 0)

def tripleB {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  retainedValue (o.1 1)

def tripleC {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  retainedValue (o.1 2)

def tripleS2 {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  tripleA τ o * tripleB τ o + tripleA τ o * tripleC τ o +
    tripleB τ o * tripleC τ o

def tripleS3 {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  tripleA τ o * tripleB τ o * tripleC τ o

def tripleDelta {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  (tripleA τ o - tripleB τ o) * (tripleB τ o - tripleC τ o) *
    (tripleC τ o - tripleA τ o)

def triplePolynomial {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ)
    (x : PrimeField p) : PrimeField p :=
  x ^ 3 + tripleS2 τ o * x - tripleS3 τ o

def deletionFactor {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  Finset.prod Z (fun z : PrimeFieldStar p => triplePolynomial τ o (z : PrimeField p))

def tripleRho {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : PrimeField p :=
  tripleDelta τ o * tripleS3 τ o * deletionFactor τ o

def tripleCircuitVector {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) :
    RetainedPoint p Z → PrimeField p :=
  fun t =>
    if t = o.1 0 then tripleB τ o - tripleC τ o
    else if t = o.1 1 then tripleC τ o - tripleA τ o
    else if t = o.1 2 then tripleA τ o - tripleB τ o
    else 0

def tripleDirection {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (τ : RetainedTriple p Z) (o : TripleOrientation τ) : Fin 3 → PrimeField p :=
  fun j =>
    if j = 0 then 1
    else if j = 1 then tripleS2 τ o
    else tripleS3 τ o

def rawStress {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    [Fintype (RetainedTriple p Z)]
    (orientation : ∀ τ : RetainedTriple p Z, TripleOrientation τ) :
    TensorProduct (PrimeField p)
      (RetainedPoint p Z → PrimeField p) (Fin 3 → PrimeField p) :=
  ∑ τ : RetainedTriple p Z,
    tripleRho τ (orientation τ) •
      TensorProduct.tmul (PrimeField p)
        (tripleCircuitVector τ (orientation τ))
        (tripleDirection τ (orientation τ))

def tensorCoordinate {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (t : RetainedPoint p Z) (j : Fin 3) :
    TensorProduct (PrimeField p)
      (RetainedPoint p Z → PrimeField p) (Fin 3 → PrimeField p) →ₗ[PrimeField p]
        PrimeField p :=
  TensorProduct.lift
    ((LinearMap.proj t).smulRight (LinearMap.proj j))

def deletionHalf (p : ℕ) : ℕ :=
  (p - 9) / 2

def residualKappa (p : ℕ) : PrimeField p :=
  2 * (-1 : PrimeField p) ^ (deletionHalf p + 1)

def deletionPolynomialAt {p : ℕ} {Z : Finset (PrimeFieldStar p)}
    (t : RetainedPoint p Z) : PrimeField p :=
  Finset.prod Z (fun z : PrimeFieldStar p => (z : PrimeField p) - retainedValue t)

/-- Claim 61341: the exact residual formula for the raw stress after one more deletion. -/
def claim61341 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    11 ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ Z : Finset (PrimeFieldStar p),
        Z.card = deletionHalf p →
          letI : Fintype (RetainedTriple p Z) := Fintype.ofFinite _
          ∀ orientation :
              ∀ τ : RetainedTriple p Z, TripleOrientation τ,
            let R := rawStress orientation
            (∀ t : RetainedPoint p Z,
              tensorCoordinate t 0 R = 0 ∧
                tensorCoordinate t 1 R =
                  residualKappa p * retainedValue t * deletionPolynomialAt t ∧
                tensorCoordinate t 2 R =
                  residualKappa p * retainedValue t ^ 2 * deletionPolynomialAt t ∧
                tensorCoordinate t 1 R ≠ 0 ∧
                tensorCoordinate t 2 R ≠ 0) ∧
              R ≠ 0

end

end MathlibPlus.Open.Research.CIElementaryAbelianOddOneMoreRawStressObstruction
