import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

abbrev Q20 := QuaternionGroup 5

def q20A : Q20 := QuaternionGroup.a 1
def q20X : Q20 := QuaternionGroup.xa 0

def q20Presentation : Prop :=
  q20A ^ 10 = 1 ∧ q20X ^ 2 = q20A ^ 5 ∧
    q20X * q20A * (q20X)⁻¹ = (q20A)⁻¹

def q20AutOrbit (g : Q20) : Set Q20 :=
  {y | ∃ φ : Q20 ≃* Q20, φ g = y}

def q20B0 : Set Q20 := {q20A ^ 5}
def q20B13 : Set Q20 := {q20A, q20A ^ 3, q20A ^ 7, q20A ^ 9}
def q20B24 : Set Q20 := {q20A ^ 2, q20A ^ 4, q20A ^ 6, q20A ^ 8}
def q20Bx : Set Q20 := {y | ∃ j : Fin 10, y = q20A ^ (j : ℕ) * q20X}

def q20BlocksDisjoint : Prop :=
  Disjoint q20B0 q20B13 ∧ Disjoint q20B0 q20B24 ∧ Disjoint q20B0 q20Bx ∧
    Disjoint q20B13 q20B24 ∧ Disjoint q20B13 q20Bx ∧ Disjoint q20B24 q20Bx

def q20OrbitClassification : Prop :=
  q20AutOrbit (q20A ^ 5) = q20B0 ∧
    q20AutOrbit q20A = q20B13 ∧
    q20AutOrbit (q20A ^ 2) = q20B24 ∧
    q20AutOrbit q20X = q20Bx ∧
    q20BlocksDisjoint ∧
    ((Set.univ : Set Q20) \ ({1} : Set Q20)) = q20B0 ∪ q20B13 ∪ q20B24 ∪ q20Bx

def q20OrdinaryConnectionSet (S : Finset Q20) : Prop :=
  (1 : Q20) ∉ S

def q20FixedByEveryAutomorphism (S : Finset Q20) : Prop :=
  ∀ φ : Q20 ≃* Q20, S.map φ.toEmbedding = S

def q20B0Finset : Finset Q20 := {q20A ^ 5}
def q20B13Finset : Finset Q20 := {q20A, q20A ^ 3, q20A ^ 7, q20A ^ 9}
def q20B24Finset : Finset Q20 := {q20A ^ 2, q20A ^ 4, q20A ^ 6, q20A ^ 8}
def q20BxFinset : Finset Q20 :=
  (Finset.univ : Finset (Fin 10)).image
    (fun j : Fin 10 => q20A ^ (j : ℕ) * q20X)

def q20UnionOfSubcollection (S : Finset Q20) : Prop :=
  ∃ e₀ e₁ e₂ e₃ : Bool,
    S = (if e₀ then q20B0Finset else ∅) ∪
      (if e₁ then q20B13Finset else ∅) ∪
      (if e₂ then q20B24Finset else ∅) ∪
      (if e₃ then q20BxFinset else ∅)

def q20FixedConnectionClassification : Prop :=
  ∀ S : Finset Q20,
    q20OrdinaryConnectionSet S →
      (q20FixedByEveryAutomorphism S ↔ q20UnionOfSubcollection S)

def q20SingletonFullAutomorphismOrbitCount : Prop :=
  Nat.card {S : Finset Q20 //
    q20OrdinaryConnectionSet S ∧ q20FixedByEveryAutomorphism S} = 16

def q20Claim : Prop :=
  q20Presentation ∧ q20OrbitClassification ∧
    q20FixedConnectionClassification ∧ q20SingletonFullAutomorphismOrbitCount

end MathlibPlus.Open.ResearchFormalization
