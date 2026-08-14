import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch.SelectorCommutators

noncomputable section

/-- A finite-support polynomial whose distinguished exponent is the `z` exponent
and whose finite multiset records the component variables. -/
abbrev FormalPolynomial (R : Type*) [Zero R] := (ℕ × Multiset ℕ) →₀ R

def fpMonomial {R : Type*} [Zero R] (r : ℕ) (parts : Multiset ℕ) (c : R) :
    FormalPolynomial R :=
  Finsupp.single (r, parts) c

def fpMul {R : Type*} [Semiring R] (P Q : FormalPolynomial R) :
    FormalPolynomial R :=
  ∑ m ∈ P.support, (∑ n ∈ Q.support,
    fpMonomial (m.1 + n.1) (m.2 + n.2) (P m * Q n))

def selector {R : Type*} [AddCommMonoid R] (s : ℕ) (P : FormalPolynomial R) :
    FormalPolynomial R :=
  ∑ m ∈ P.support,
    fpMonomial 0 ((m.1 + s) ::ₘ m.2) (P m)

/-- The `t`-valued component derivative, with `t` represented by `Polynomial.X`. -/
def derivativeSelector {R : Type*} [CommRing R] (P : FormalPolynomial R) :
    FormalPolynomial (Polynomial R) :=
  ∑ m ∈ P.support, (∑ j ∈ (m.2.toFinset.filter (fun j => 0 < j)),
      fpMonomial m.1 (m.2.erase j)
        (Polynomial.C (P m) * Polynomial.C (m.2.count j : R) *
          Polynomial.X ^ (j - 1)))

def substituteZ {R : Type*} [CommRing R] (P : FormalPolynomial R) :
    FormalPolynomial (Polynomial R) :=
  ∑ m ∈ P.support,
    fpMonomial 0 m.2 (Polynomial.C (P m) * Polynomial.X ^ m.1)

def coefficientLift {R : Type*} [CommRing R] (P : FormalPolynomial R) :
    FormalPolynomial (Polynomial R) :=
  ∑ m ∈ P.support, fpMonomial m.1 m.2 (Polynomial.C (P m))

def fpScale {R : Type*} [CommRing R] (q : Polynomial R)
    (P : FormalPolynomial (Polynomial R)) : FormalPolynomial (Polynomial R) :=
  ∑ m ∈ P.support, fpMonomial m.1 m.2 (q * P m)

/-- The selector commutator, stated for every positive selector index and every
finite polynomial in `z` and the component variables. -/
def selector_commutator_identity : Prop :=
  ∀ (R : Type*) [CommRing R] (s : ℕ) (_hs : 1 ≤ s) (H : FormalPolynomial R),
    derivativeSelector (selector s H) =
      selector s (derivativeSelector H) +
        fpScale (Polynomial.X ^ (s - 1)) (substituteZ H)

/-- The balanced bicentroid product. -/
def bicentroidProduct {R : Type*} [Semiring R]
    (P Q : FormalPolynomial R) : FormalPolynomial R :=
  fpMul (selector 1 P) (selector 1 Q) + selector 2 (fpMul P Q)

def bicentroidCommutator {R : Type*} [CommRing R]
    (P Q : FormalPolynomial R) : FormalPolynomial (Polynomial R) :=
  derivativeSelector (bicentroidProduct P Q) -
    bicentroidProduct (derivativeSelector P) (coefficientLift Q) -
    bicentroidProduct (coefficientLift P) (derivativeSelector Q)

/-- The bilinear selector commutator identity in the same polynomial model. -/
def bicentroid_selector_commutator_identity : Prop :=
  ∀ (R : Type*) [CommRing R] (P Q : FormalPolynomial R),
    bicentroidCommutator P Q =
      fpMul (substituteZ P) (coefficientLift (selector 1 Q)) +
        fpMul (coefficientLift (selector 1 P)) (substituteZ Q) +
        fpScale Polynomial.X (fpMul (substituteZ P) (substituteZ Q))

end

end MathlibPlus.Open.ResearchBatch.SelectorCommutators
