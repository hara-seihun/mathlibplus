import Mathlib

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

namespace MathlibPlus.Open.Research.R0366Claim20485

abbrev Cell (r : ℕ) := Finset (Fin r)
abbrev NonemptyCell (r : ℕ) := {S : Cell r // S.Nonempty}
abbrev HarmonicVariable (r : ℕ) := Option (NonemptyCell r)

def rootCell {V : Type*} [Fintype V] {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) (v : V) : Cell r :=
  Finset.univ.filter (fun i => G.Adj (x i) v)

def rootHasInternalGraph {V : Type*} {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) (A : SimpleGraph (Fin r)) : Prop :=
  Function.Injective x ∧
    ∀ i j : Fin r, A.Adj i j ↔ G.Adj (x i) (x j)

def rootDominates {V : Type*} {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) : Prop :=
  ∀ v : V, v ∈ Set.range x ∨ ∃ i : Fin r, G.Adj (x i) v

def rootMonomial {V : Type*} [Fintype V] {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) : MvPolynomial (Cell r) ℚ :=
  ∏ v : {v : V // v ∉ Set.range x},
    MvPolynomial.X (rootCell G x v.1)

def profilePolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (A : SimpleGraph (Fin r)) :
    MvPolynomial (Cell r) ℚ :=
  ∑ x : {x : Fin r → V // rootHasInternalGraph G x A},
    rootMonomial G x.1

def profilePolynomialHomogeneous {σ : Type*}
    (p : MvPolynomial σ ℚ) (d : ℕ) : Prop :=
  MvPolynomial.IsHomogeneous p d

def cardDirectionalDerivative {r : ℕ}
    (p : MvPolynomial (Cell r) ℚ) : MvPolynomial (Cell r) ℚ :=
  ∑ S : Cell r, MvPolynomial.pderiv S p

def coordinateChange {r : ℕ} :
    MvPolynomial (HarmonicVariable r) ℚ → MvPolynomial (Cell r) ℚ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun q => match q with
      | none => MvPolynomial.X (∅ : Cell r)
      | some S => MvPolynomial.X S.1 - MvPolynomial.X (∅ : Cell r))

def harmonicLift {r : ℕ} :
    MvPolynomial (NonemptyCell r) ℚ → MvPolynomial (HarmonicVariable r) ℚ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun S => MvPolynomial.X (some S))

def boundaryRestriction {r : ℕ} :
    MvPolynomial (Cell r) ℚ → MvPolynomial (NonemptyCell r) ℚ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun S => if h : S.Nonempty then MvPolynomial.X ⟨S, h⟩ else 0)

def freePolynomial {r : ℕ} :
    MvPolynomial (NonemptyCell r) ℚ → MvPolynomial (NonemptyCell r) ℚ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C) (fun S => MvPolynomial.X S)

def boundaryRootMonomial {V : Type*} [Fintype V] {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) :
    MvPolynomial (NonemptyCell r) ℚ :=
  boundaryRestriction (rootMonomial G x)

def dominatingRootBoundary {V : Type*} [Fintype V] {r : ℕ}
    (G : SimpleGraph V) (A : SimpleGraph (Fin r)) :
    MvPolynomial (NonemptyCell r) ℚ :=
  ∑ x : {x : Fin r → V //
      rootHasInternalGraph G x A ∧ rootDominates G x},
    boundaryRootMonomial G x.1

def dominationBoundaryIsCompleteKernel20485 : Prop :=
  ∀ (n r : ℕ), 1 ≤ r → r < n →
    (∀ (G : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r)),
      boundaryRestriction (profilePolynomial G A) =
        dominatingRootBoundary G A) ∧
    (∀ B : MvPolynomial (NonemptyCell r) ℚ,
      profilePolynomialHomogeneous B (n - r) →
        cardDirectionalDerivative (coordinateChange (harmonicLift B)) = 0 ∧
          boundaryRestriction (coordinateChange (harmonicLift B)) =
            freePolynomial B) ∧
    (∀ Q : MvPolynomial (Cell r) ℚ,
      profilePolynomialHomogeneous Q (n - r) →
      cardDirectionalDerivative Q = 0 →
        ∃! B : MvPolynomial (NonemptyCell r) ℚ,
          Q = coordinateChange (harmonicLift B) ∧
            profilePolynomialHomogeneous B (n - r) ∧
            boundaryRestriction Q = freePolynomial B)

end MathlibPlus.Open.Research.R0366Claim20485
