import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev C7 := ZMod 7
abbrev C3 := ZMod 3
abbrev C2 := ZMod 2
abbrev S3 := Additive (Equiv.Perm (Fin 3))
abbrev Order42 := C7 × S3
abbrev Order42Coordinates := C7 × C3 × C2

/-- The explicit C₇ × C₃ ⋊ C₂ coordinate multiplication. -/
def c21SemidirectC2Product
    (x y : Order42Coordinates) : Order42Coordinates :=
  (x.1 + y.1,
    x.2.1 + (-1 : C3) ^ (x.2.2.val : Nat) * y.2.1,
    x.2.2 + y.2.2)

def coordinateModel (coord : Order42Coordinates ≃ Order42) : Prop :=
  ∀ x y, coord (c21SemidirectC2Product x y) = coord x + coord y

/-- Claim 27820: C₇ × S₃ has the displayed C₇ × C₃ ⋊ C₂ coordinates. -/
def claim_27820 : Prop :=
  ∃ coord : Order42Coordinates ≃ Order42, coordinateModel coord

def inverseAtom (g : Order42) : Finset Order42 := {g, -g}

def inverseAtoms : Finset (Finset Order42) :=
  ((Finset.univ : Finset Order42).filter (fun g => g ≠ 0)).image inverseAtom

def inverseClosed (A : Finset Order42) : Prop :=
  ∀ g, g ∈ A → -g ∈ A

noncomputable def connectionSets : Finset (Finset Order42) := by
  classical
  exact
    (Finset.univ : Finset Order42).powerset.filter
      (fun A => 0 ∉ A ∧ inverseClosed A)

def nonidentityInvolutions : Finset Order42 :=
  (Finset.univ : Finset Order42).filter (fun g => g ≠ 0 ∧ g = -g)

def pairedInverseAtoms : Finset (Finset Order42) :=
  inverseAtoms.filter (fun A => A.card = 2)

/-- Claim 27821: the nonidentity inverse atoms and inverse-closed sets have the
advertised cardinalities. -/
def claim_27821 : Prop :=
  Fintype.card {g : Order42 // g ≠ 0} = 41 ∧
    nonidentityInvolutions.card = 3 ∧
    pairedInverseAtoms.card = 19 ∧
    inverseAtoms.card = 22 ∧
    (∀ g : Order42, g ≠ 0 →
      g ∈ nonidentityInvolutions ∨
        ∃ A, A ∈ pairedInverseAtoms ∧ g ∈ A) ∧
    connectionSets.card = 4194304

def coordinateAutomorphismFormula
    (coord : Order42Coordinates ≃ Order42) : Prop :=
  ∀ φ : Order42 ≃+ Order42,
    ∃ u7 : C7, ∃ u3 : C3, ∃ v : C3,
      u7 ≠ 0 ∧ u3 ≠ 0 ∧
        ∀ z : C7, ∀ r : C3, ∀ e : C2,
          coord.symm (φ (coord (z, r, e))) =
            (u7 * z, u3 * r + v * ((e.val : Nat) : C3), e)

def faithfulAtomAction : Prop :=
  ∀ φ ψ : Order42 ≃+ Order42,
    (∀ A : Finset Order42, A ∈ inverseAtoms →
      A.image φ = A.image ψ) →
    φ = ψ

/-- Claim 27822: all automorphisms have the displayed coordinate form, the
automorphism group has order 36, and its action on inverse atoms is faithful. -/
def claim_27822 : Prop :=
  (∃ coord : Order42Coordinates ≃ Order42,
    coordinateModel coord ∧ coordinateAutomorphismFormula coord) ∧
    Fintype.card (Order42 ≃+ Order42) = 36 ∧
    faithfulAtomAction

end MathlibPlus.Open.ResearchFormalization
