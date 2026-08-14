import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section

abbrev C3Squared := Multiplicative (Fin 2 → ZMod 3)
abbrev C3SquaredD10 := C3Squared × DihedralGroup 5

/-- A singleton inverse atom is a nonidentity element fixed by inversion. -/
def singletonInverseAtom {G : Type*} [DecidableEq G] [Group G] (A : Finset G) : Prop :=
  ∃ g : G, g ≠ 1 ∧ g⁻¹ = g ∧ A = ({g} : Finset G)

/-- A paired inverse atom is the two-element inversion orbit of a
nonidentity noninvolution. -/
def pairedInverseAtom {G : Type*} [DecidableEq G] [Group G] (A : Finset G) : Prop :=
  ∃ g : G, g ≠ 1 ∧ g⁻¹ ≠ g ∧ A = ({g, g⁻¹} : Finset G)

/-- Claim 43736: the fixed group `C₃² × D₁₀` has the stated atom counts and
full automorphism-group order. -/
def c3SquareD10AtomAndAutFacts : Prop :=
  let G := C3SquaredD10
  Nat.card G = 90 ∧
  Nat.card {A : Finset G // singletonInverseAtom A} = 5 ∧
  Nat.card {A : Finset G // pairedInverseAtom A} = 42 ∧
  Nat.card (G ≃* G) = 960

end

end MathlibPlus.Open.GraphTheory
