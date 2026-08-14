import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch01_01a000fb_3b4f_79ef_9098_771f8cd25d71

noncomputable section

namespace R5262

abbrev F5 := ZMod 5
abbrev V3 := Fin 3 → F5
abbrev V := V3 × V3

/-- The polynomial map in the admitted R-5262 construction. -/
def F (z : V3) : V3 :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

/-- The coupled map is written on pairs `(x,z)`, as in the admitted claim. -/
def q (v : V) : V :=
  (v.2, v.1 + F v.2)

def qInv (v : V) : V :=
  (v.2 - F v.1, v.1)

def qEquiv : V ≃ V where
  toFun := q
  invFun := qInv
  left_inv := by
    intro v
    simp [q, qInv]
  right_inv := by
    intro v
    simp [q, qInv]

def e1 : V3 := ![1, 0, 0]
def e2 : V3 := ![0, 1, 0]
def e3 : V3 := ![0, 0, 1]
def e23 : V3 := ![0, 1, 1]

def displayedLabels : Finset V3 :=
  {e1, e2, e3, e23, -e1, -e2, -e3, -e23}

def mixedPlus (z a : V3) : V3 :=
  F (a + z) - F a - F z

def mixedMinus (z a : V3) : V3 :=
  F (a - z) - F a - F (-z)

def W (z : V3) : Submodule F5 V3 :=
  Submodule.span F5 (Set.range (mixedPlus z) ∪ Set.range (mixedMinus z))

def S : Set V :=
  {v | ∃ z, z ∈ displayedLabels ∧ ∃ w, w ∈ W z ∧ v = (w, z)}

def inverseSet (A : Set V) : Set V :=
  {v | -v ∈ A}

def fibreDimensionList : List ℕ :=
  [Module.finrank F5 (W e1), Module.finrank F5 (W e2), Module.finrank F5 (W e3),
    Module.finrank F5 (W e23)]

def pairedFibreSize (z : V3) : ℕ :=
  Nat.card (W z) + Nat.card (W (-z))

def pairedFibreSizeList : List ℕ :=
  [pairedFibreSize e1, pairedFibreSize e2, pairedFibreSize e3,
    pairedFibreSize e23]

/-- Exact formal surface of R-5262 S1. -/
def claim55074 : Prop :=
  (∀ (x z : V3), q (x, z) = (z, x + F z)) ∧
    (∀ z, W z = Submodule.span F5
      (Set.range (mixedPlus z) ∪ Set.range (mixedMinus z))) ∧
    (∀ v, v ∈ S ↔ ∃ z, z ∈ displayedLabels ∧
      ∃ w, w ∈ W z ∧ v = (w, z))

/-- Exact formal surface of the numerical and closure assertions in R-5262 S2. -/
def claim55076 : Prop :=
  fibreDimensionList = [1, 2, 2, 3] ∧
    pairedFibreSizeList = [10, 50, 50, 250] ∧
    Nat.card {v : V // v ∈ S} = 360 ∧
    (0 : V) ∉ S ∧
    S = inverseSet S ∧
    Submodule.span F5 S = ⊤

def cayleyAdj (A : Set V) (u v : V) : Prop :=
  v - u ∈ A

def qTransport : Prop :=
  ∀ x y, cayleyAdj S x y ↔ cayleyAdj (q '' S) (q x) (q y)

def graphAutomorphism (A : Set V) (g : Equiv.Perm V) : Prop :=
  ∀ x y, cayleyAdj A (g x) (g y) ↔ cayleyAdj A x y

def translation (a : V) : Equiv.Perm V where
  toFun := fun x => x + a
  invFun := fun x => x - a
  left_inv := by intro x; simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  right_inv := by intro x; simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

def inversion : Equiv.Perm V where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := by intro x; simp
  right_inv := by intro x; simp

def R : Set (Equiv.Perm V) :=
  {g | ∃ a, g = translation a}

def conjugateByQ (g : Equiv.Perm V) : Equiv.Perm V :=
  (qEquiv.symm.trans g).trans qEquiv

def T : Set (Equiv.Perm V) :=
  {g | ∃ r, r ∈ R ∧ g = conjugateByQ r}

def jR : Equiv.Perm V := inversion

def jT : Equiv.Perm V := conjugateByQ inversion

/-- Exact formal surface of R-5262 S3. -/
def claim55078 : Prop :=
  qTransport ∧
    q '' S = inverseSet (q '' S) ∧
    (∀ g, g ∈ R → graphAutomorphism S g) ∧
    (∀ g, g ∈ T → graphAutomorphism S g) ∧
    graphAutomorphism S jR ∧
    graphAutomorphism S jT

end R5262

namespace R5489

abbrev V (p r : ℕ) := Fin r → ZMod p

/-- Nonzero vectors modulo the relation identifying a direction with its negative. -/
def oppositeSetoid (p r : ℕ) : Setoid {v : V p r // v ≠ 0} where
  r a b := (a : V p r) = (b : V p r) ∨ (a : V p r) = -(b : V p r)
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        simp
    · intro a b c hab hbc
      rcases hab with hab | hab <;> rcases hbc with hbc | hbc
      · exact Or.inl (hab.trans hbc)
      · right
        calc
          (a : V p r) = (b : V p r) := hab
          _ = -(c : V p r) := hbc
      · right
        calc
          (a : V p r) = -(b : V p r) := hab
          _ = -(c : V p r) := by simpa using congrArg Neg.neg hbc
      · left
        calc
          (a : V p r) = -(b : V p r) := hab
          _ = -(-(c : V p r)) := by simpa using congrArg Neg.neg hbc
          _ = (c : V p r) := by simp

abbrev D (p r : ℕ) := Quotient (oppositeSetoid p r)

def unorderedPair (x y : V p r) : Finset (V p r) := {x, y}

def atom (c : D p r) : Set (Finset (V p r)) :=
  {A | ∃ d : {v : V p r // v ≠ 0}, ∃ x : V p r,
    Quotient.mk (oppositeSetoid p r) d = c ∧ A = unorderedPair x (x + d.1)}

def unorderedPairs : Set (Finset (V p r)) :=
  {A | A.card = 2}

def inverseClosed (S : Set (V p r)) : Prop :=
  ∀ v, v ∈ S ↔ -v ∈ S

def cayleyEdges (S : Set (V p r)) : Set (Finset (V p r)) :=
  {A | A.card = 2 ∧ ∃ x y, A = unorderedPair x y ∧ y - x ∈ S}

def labelsIn (S : Set (V p r)) : Set (D p r) :=
  {c | ∃ d : {v : V p r // v ≠ 0}, Quotient.mk (oppositeSetoid p r) d = c ∧ d.1 ∈ S}

def atomPartition (p r : ℕ) : Prop :=
  (∀ c : D p r, atom c ⊆ unorderedPairs) ∧
    (⋃ c : D p r, atom c) = unorderedPairs ∧
    (∀ c₁ c₂ : D p r, c₁ ≠ c₂ → Disjoint (atom c₁) (atom c₂))

/-- Exact formal surface of R-5489 S1. -/
def claim55105 : Prop :=
  ∀ (p r : ℕ), p.Prime → Odd p →
    atomPartition p r ∧
      (∀ S : Set (V p r), inverseClosed S →
        cayleyEdges S = ⋃ c ∈ labelsIn S, atom c)

end R5489

end

end MathlibPlus.Open.ResearchFormalization.Batch01_01a000fb_3b4f_79ef_9098_771f8cd25d71
