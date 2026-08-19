import Mathlib

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

namespace MathlibPlus.Open.Research.R0366Claim20484

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

def rootMonomial {V : Type*} [Fintype V] {r : ℕ}
    (G : SimpleGraph V) (x : Fin r → V) : MvPolynomial (Cell r) ℚ :=
  ∏ v : {v : V // v ∉ Set.range x},
    MvPolynomial.X (rootCell G x v.1)

def profilePolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (A : SimpleGraph (Fin r)) :
    MvPolynomial (Cell r) ℚ :=
  ∑ x : {x : Fin r → V // rootHasInternalGraph G x A},
    rootMonomial G x.1

def cardGraph {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph {u : V // u ≠ v} :=
  G.induce {u : V | u ≠ v}

def vertexDeckEqual {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    ∀ v : Fin n,
      Nonempty (cardGraph G v ≃g cardGraph H (σ v))

def profileDifference {n r : ℕ}
    (G H : SimpleGraph (Fin n)) (A : SimpleGraph (Fin r)) :
    MvPolynomial (Cell r) ℚ :=
  profilePolynomial G A - profilePolynomial H A

def cardDirectionalDerivative {r : ℕ}
    (p : MvPolynomial (Cell r) ℚ) : MvPolynomial (Cell r) ℚ :=
  ∑ S : Cell r, MvPolynomial.pderiv S p

def profilePolynomialHomogeneous {σ : Type*}
    (p : MvPolynomial σ ℚ) (d : ℕ) : Prop :=
  MvPolynomial.IsHomogeneous p d

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

def exactKernelNormalForm20484 : Prop :=
  ∀ (n r : ℕ), 1 ≤ r → r < n →
    cardDirectionalDerivative (MvPolynomial.X (∅ : Cell r)) = 1 ∧
    (∀ S : NonemptyCell r,
      cardDirectionalDerivative
        (MvPolynomial.X S.1 - MvPolynomial.X (∅ : Cell r)) = 0) ∧
    (∀ P : MvPolynomial (HarmonicVariable r) ℚ,
      cardDirectionalDerivative (coordinateChange P) =
        coordinateChange (MvPolynomial.pderiv none P)) ∧
    (∀ G H : SimpleGraph (Fin n), vertexDeckEqual G H →
      ∀ A : SimpleGraph (Fin r),
        profilePolynomialHomogeneous (profileDifference G H A) (n - r) →
        cardDirectionalDerivative (profileDifference G H A) = 0 →
        ∃! B : MvPolynomial (NonemptyCell r) ℚ,
          profileDifference G H A = coordinateChange (harmonicLift B) ∧
            profilePolynomialHomogeneous B (n - r))

end MathlibPlus.Open.Research.R0366Claim20484
