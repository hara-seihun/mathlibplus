import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.TNCompounds

noncomputable section

abbrev Subsets (n s : Nat) := {I : Finset (Fin n) // I.card = s}

noncomputable instance (n s : Nat) : Fintype (Subsets n s) := Fintype.ofFinite _

def finiteMinor {n m : Nat} {R : Type} [CommRing R]
    (M : Matrix (Fin n) (Fin m) R)
    (I : Finset (Fin n)) (J : Finset (Fin m)) (h : I.card = J.card) : R :=
  Matrix.det
    (M.submatrix
      (fun i => ((Finset.orderIsoOfFin I rfl) i : Fin n))
      (fun j => ((Finset.orderIsoOfFin J h.symm) j : Fin m)))

def compound {n m : Nat} {R : Type} [CommRing R]
    (M : Matrix (Fin n) (Fin m) R) (s : Nat) :
    Matrix (Subsets n s) (Subsets m s) R :=
  fun I J => finiteMinor M I.1 J.1 (I.2.trans J.2.symm)

def allMinorsIn {n m : Nat} {R : Type} [CommRing R]
    (M : Matrix (Fin n) (Fin m) R) (S : Subsemiring R) : Prop :=
  ∀ s (I : Subsets n s) (J : Subsets m s), compound M s I J ∈ S

def positiveCoordinates {α R : Type} [CommRing R]
    (S : Subsemiring R) (v : α → R) : Prop :=
  ∀ i, v i ∈ S

def compoundMapsPositive {n m : Nat} {R : Type} [CommRing R]
    (M : Matrix (Fin n) (Fin m) R) (S : Subsemiring R) : Prop :=
  ∀ s (v : Subsets m s → R),
    positiveCoordinates S v →
      positiveCoordinates S (fun I => ∑ J, compound M s I J * v J)

def claim46082 : Prop :=
  ∀ {R : Type} [CommRing R] (S : Subsemiring R)
    (n m p : Nat)
    (M : Matrix (Fin n) (Fin m) R)
    (N : Matrix (Fin m) (Fin p) R),
    (∀ s, compound (M * N) s = compound M s * compound N s) ∧
      (allMinorsIn M S ↔ compoundMapsPositive M S)

end

end MathlibPlus.Open.TNCompounds
