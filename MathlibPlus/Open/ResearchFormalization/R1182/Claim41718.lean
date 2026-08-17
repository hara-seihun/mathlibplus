import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41718

abbrev Q12 := ZMod 3 × ZMod 4
abbrev G156 := ZMod 13 × Q12

def q12Parity (i : ZMod 4) : ZMod 3 :=
  (-1 : ZMod 3) ^ i.val

def q12Mul (x y : Q12) : Q12 :=
  (x.1 + q12Parity x.2 * y.1, x.2 + y.2)

def q12One : Q12 := (0, 0)

def q12Inv (x : Q12) : Q12 :=
  (-q12Parity x.2 * x.1, -x.2)

def q12Chi (h : Q12) : ZMod 13 :=
  (-1 : ZMod 13) ^ h.2.val

def g156Mul (x y : G156) : G156 :=
  (x.1 + q12Chi x.2 * y.1, q12Mul x.2 y.2)

def g156Inv (x : G156) : G156 :=
  (-q12Chi x.2 * x.1, q12Inv x.2)

def q12U : Set Q12 :=
  {h | h.1 = 1 ∨ h.1 = 2}

def g156S : Set G156 :=
  {x | x.1 = 0 ∧ x.2 ∈ q12U}

def inverseClosed (S : Set G156) : Prop :=
  ∀ x : G156, x ∈ S ↔ g156Inv x ∈ S

def q12Adj (h k : Q12) : Prop :=
  q12Mul k (q12Inv h) ∈ q12U

def g156Adj (x y : G156) : Prop :=
  g156Mul y (g156Inv x) ∈ g156S

def coordinateChart (x : G156) : G156 :=
  (q12Chi x.2 * x.1, x.2)

def chartAdj (x y : G156) : Prop :=
  g156Adj (coordinateChart x) (coordinateChart y)

def disjointQuotientCopies : Prop :=
  Function.Bijective coordinateChart ∧
    ∀ (c d : ZMod 13) (h k : Q12),
      chartAdj (c, h) (d, k) ↔
        (c = d ∧ q12Adj h k)

def connectedRelation {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ x y, Relation.ReflTransGen r x y

noncomputable def relationValency {α : Type*} (r : α → α → Prop) (x : α) : Nat :=
  Set.ncard {y | r x y}

noncomputable def orderedEdgeCount {α : Type*} (r : α → α → Prop) : Nat :=
  Set.ncard {p : α × α | r p.1 p.2}

noncomputable def edgeCount {α : Type*} (r : α → α → Prop) : Nat :=
  orderedEdgeCount r / 2

def axisAtom : Set Q12 :=
  {h | h.1 = 0 ∧ h ≠ q12One}

def outerAtom : Set Q12 :=
  {h | h.1 ≠ 0}

def completeProjectedAtom (T : Set Q12) : Prop :=
  T = ({q12One} : Set Q12) ∨ T = axisAtom ∨ T = outerAtom

def projectedOrbital (T : Set Q12) : Set (Q12 × Q12) :=
  {p | q12Mul p.2 (q12Inv p.1) ∈ T}

def quotientOrbital : Set (Q12 × Q12) :=
  projectedOrbital outerAtom

def q12Point (n : Nat) : Q12 :=
  (((n - 1) % 3 : Nat), ((n - 1) / 3 : Nat))

def diagonalOrbital (A : Subgroup (Equiv.Perm Q12))
    (p : Q12 × Q12) : Set (Q12 × Q12) :=
  {q | ∃ g : A,
    ((g : Equiv.Perm Q12) p.1, (g : Equiv.Perm Q12) p.2) = q}

noncomputable def orbitalSizes (A : Subgroup (Equiv.Perm Q12)) : Set Nat :=
  {n | ∃ p : Q12 × Q12, n = Set.ncard (diagonalOrbital A p)}

-- Concrete degree-twelve permutation carriers for the two exceptional rows.
def exceptionalAmbient127 : Subgroup (Equiv.Perm Q12) :=
  Subgroup.closure {
    (Equiv.swap (q12Point 1) (q12Point 10)) *
      (Equiv.swap (q12Point 3) (q12Point 9)) *
      (Equiv.swap (q12Point 4) (q12Point 7)) *
      (Equiv.swap (q12Point 5) (q12Point 11)),
    (Equiv.swap (q12Point 1) (q12Point 7) *
      Equiv.swap (q12Point 7) (q12Point 10)) *
      (Equiv.swap (q12Point 2) (q12Point 6) *
        Equiv.swap (q12Point 6) (q12Point 8)) *
      (Equiv.swap (q12Point 3) (q12Point 11) *
        Equiv.swap (q12Point 11) (q12Point 5)),
    (Equiv.swap (q12Point 1) (q12Point 6) *
      Equiv.swap (q12Point 6) (q12Point 5)) *
      (Equiv.swap (q12Point 2) (q12Point 11) *
        Equiv.swap (q12Point 11) (q12Point 10)) *
      (Equiv.swap (q12Point 3) (q12Point 7) *
        Equiv.swap (q12Point 7) (q12Point 8)) *
      (Equiv.swap (q12Point 4) (q12Point 12) *
        Equiv.swap (q12Point 12) (q12Point 9)),
    (Equiv.swap (q12Point 1) (q12Point 2)) *
      (Equiv.swap (q12Point 4) (q12Point 12)) *
      (Equiv.swap (q12Point 5) (q12Point 11)) *
      (Equiv.swap (q12Point 6) (q12Point 10)) *
      (Equiv.swap (q12Point 7) (q12Point 8))}

def exceptionalAmbient204 : Subgroup (Equiv.Perm Q12) :=
  Subgroup.closure {
    (Equiv.swap (q12Point 3) (q12Point 9)) *
      (Equiv.swap (q12Point 5) (q12Point 11)),
    (Equiv.swap (q12Point 3) (q12Point 5)) *
      (Equiv.swap (q12Point 9) (q12Point 11)),
    (Equiv.swap (q12Point 2) (q12Point 12) *
      Equiv.swap (q12Point 12) (q12Point 8)) *
      (Equiv.swap (q12Point 3) (q12Point 11) *
        Equiv.swap (q12Point 11) (q12Point 9)) *
      (Equiv.swap (q12Point 4) (q12Point 7) *
        Equiv.swap (q12Point 7) (q12Point 10)),
    (Equiv.swap (q12Point 1) (q12Point 6) *
      Equiv.swap (q12Point 6) (q12Point 5)) *
      (Equiv.swap (q12Point 2) (q12Point 11) *
        Equiv.swap (q12Point 11) (q12Point 10)) *
      (Equiv.swap (q12Point 3) (q12Point 7) *
        Equiv.swap (q12Point 7) (q12Point 8)) *
      (Equiv.swap (q12Point 4) (q12Point 12) *
        Equiv.swap (q12Point 12) (q12Point 9)),
    (Equiv.swap (q12Point 1) (q12Point 2)) *
      (Equiv.swap (q12Point 4) (q12Point 12)) *
      (Equiv.swap (q12Point 5) (q12Point 11)) *
      (Equiv.swap (q12Point 6) (q12Point 10)) *
      (Equiv.swap (q12Point 7) (q12Point 8))}

def selectedOrbital (A : Subgroup (Equiv.Perm Q12)) : Set (Q12 × Q12) :=
  diagonalOrbital A (q12Point 1, q12Point 2)

def claim41718 : Prop :=
  inverseClosed g156S ∧
    Fintype.card Q12 = 12 ∧
    Fintype.card G156 = 156 ∧
    disjointQuotientCopies ∧
    connectedRelation q12Adj ∧
    (∀ h : Q12, relationValency q12Adj h = 8) ∧
    edgeCount g156Adj = 624 ∧
    Set.ncard quotientOrbital = 96 ∧
    selectedOrbital exceptionalAmbient127 = quotientOrbital ∧
    selectedOrbital exceptionalAmbient204 = quotientOrbital ∧
    orbitalSizes exceptionalAmbient127 = ({12, 36, 96} : Set Nat) ∧
    orbitalSizes exceptionalAmbient204 = ({12, 36, 96} : Set Nat)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41718
