import Mathlib

noncomputable section

namespace MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722

abbrev Q12 := ZMod 3 × ZMod 4
abbrev G156 := ZMod 13 × Q12

/-- The parity character in the displayed `F₃⁺ ⋊ C₄` model. -/
def q12Chi (h : Q12) : ZMod 3 := (-1 : ZMod 3) ^ h.2.val

/-- The same parity character acting on the `C₁₃` fibre. -/
def q156Chi (h : Q12) : ZMod 13 := (-1 : ZMod 13) ^ h.2.val

def q12Mul (h k : Q12) : Q12 :=
  (h.1 + q12Chi h * k.1, h.2 + k.2)

def q12One : Q12 := (0, 0)

def q12Inv (h : Q12) : Q12 :=
  (-q12Chi h * h.1, -h.2)

def g156Mul (x y : G156) : G156 :=
  (x.1 + q156Chi x.2 * y.1, q12Mul x.2 y.2)

def g156One : G156 := (0, q12One)

def g156Inv (x : G156) : G156 :=
  (-q156Chi x.2 * x.1, q12Inv x.2)

def q12U : Set Q12 :=
  {h | h.1 = 1 ∨ h.1 = 2}

def g156S : Set G156 :=
  {x | x.1 = 0 ∧ x.2 ∈ q12U}

/-- The left-Cayley relation used by the twisted coordinate chart. -/
def quotientAdj (h k : Q12) : Prop :=
  q12Mul k (q12Inv h) ∈ q12U

def groupCayleyAdj (x y : G156) : Prop :=
  g156Mul y (g156Inv x) ∈ g156S

def coordinateChart (x : G156) : G156 :=
  (q156Chi x.2 * x.1, x.2)

def recognitionAdj (x y : G156) : Prop :=
  groupCayleyAdj (coordinateChart x) (coordinateChart y)

def inverseClosed (S : Set G156) : Prop :=
  ∀ s, s ∈ S ↔ g156Inv s ∈ S

def relationAutomorphism {α : Type*}
    (r : α → α → Prop) (f : Equiv.Perm α) : Prop :=
  ∀ x y, r x y ↔ r (f x) (f y)

def connectedRelation {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ x y, Relation.ReflTransGen r x y

def relationValency {α : Type*} (r : α → α → Prop) (x : α) : Nat :=
  Set.ncard {y | r x y}

def orderedRelationEdges {α : Type*} (r : α → α → Prop) : Nat :=
  Set.ncard {p : α × α | r p.1 p.2}

def q12OrbitalSet : Set (Q12 × Q12) :=
  {p | quotientAdj p.1 p.2}

def q12Point (n : Nat) : Q12 :=
  (((n - 1) % 3 : Nat), ((n - 1) / 3 : Nat))

def diagonalOrbital (A : Subgroup (Equiv.Perm Q12))
    (p : Q12 × Q12) : Set (Q12 × Q12) :=
  {q | ∃ g : A,
    ((g : Equiv.Perm Q12) p.1, (g : Equiv.Perm Q12) p.2) = q}

def orbitalSizes (A : Subgroup (Equiv.Perm Q12)) : Set Nat :=
  {n | ∃ p : Q12 × Q12, n = Set.ncard (diagonalOrbital A p)}

/-- The first exceptional degree-twelve permutation group, in the fixed
abstract coordinates used by the Q₁₂ model. -/
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

/-- The exact selected quotient graph has thirteen twisted components. -/
def disjointQuotientCopies : Prop :=
  ∀ c d : ZMod 13, ∀ h k : Q12,
    recognitionAdj (c, h) (d, k) ↔
      (c = d ∧ quotientAdj h k)

def claim41718 : Prop :=
  inverseClosed g156S ∧
    disjointQuotientCopies ∧
    connectedRelation quotientAdj ∧
    (∀ h : Q12, relationValency quotientAdj h = 8) ∧
    orderedRelationEdges recognitionAdj = 1248 ∧
    orderedRelationEdges recognitionAdj / 2 = 624 ∧
    Set.ncard q12OrbitalSet = 96 ∧
    selectedOrbital exceptionalAmbient127 = q12OrbitalSet ∧
    selectedOrbital exceptionalAmbient204 = q12OrbitalSet ∧
    orbitalSizes exceptionalAmbient127 = {12, 36, 96} ∧
    orbitalSizes exceptionalAmbient204 = {12, 36, 96}

def quotientAutomorphism (q : Equiv.Perm Q12) : Prop :=
  relationAutomorphism quotientAdj q

def wreathMember (f : Equiv.Perm G156) : Prop :=
  ∃ σ : Equiv.Perm (ZMod 13),
    ∀ c : ZMod 13, ∃ q : Equiv.Perm Q12,
      quotientAutomorphism q ∧
      ∀ h : Q12, f (c, h) = (σ c, q h)

def claim41719 : Prop :=
  ∀ f : Equiv.Perm G156,
    relationAutomorphism recognitionAdj f ↔ wreathMember f

/-- The three explicit regular Q₁₂ coordinate copies used in the exceptional
cross-class pairs. -/
def classX1 : Equiv.Perm Q12 :=
  (Equiv.swap (q12Point 1) (q12Point 2) *
      Equiv.swap (q12Point 2) (q12Point 3)) *
    (Equiv.swap (q12Point 4) (q12Point 6) *
      Equiv.swap (q12Point 6) (q12Point 5)) *
    (Equiv.swap (q12Point 7) (q12Point 8) *
      Equiv.swap (q12Point 8) (q12Point 9)) *
    (Equiv.swap (q12Point 10) (q12Point 12) *
      Equiv.swap (q12Point 12) (q12Point 11))

def classY1 : Equiv.Perm Q12 :=
  (Equiv.swap (q12Point 1) (q12Point 4) *
      Equiv.swap (q12Point 4) (q12Point 7) *
      Equiv.swap (q12Point 7) (q12Point 10)) *
    (Equiv.swap (q12Point 2) (q12Point 5) *
      Equiv.swap (q12Point 5) (q12Point 8) *
      Equiv.swap (q12Point 8) (q12Point 11)) *
    (Equiv.swap (q12Point 3) (q12Point 6) *
      Equiv.swap (q12Point 6) (q12Point 9) *
      Equiv.swap (q12Point 9) (q12Point 12))

def classX2 : Equiv.Perm Q12 :=
  (Equiv.swap (q12Point 1) (q12Point 2) *
      Equiv.swap (q12Point 2) (q12Point 3)) *
    (Equiv.swap (q12Point 4) (q12Point 12) *
      Equiv.swap (q12Point 12) (q12Point 9)) *
    (Equiv.swap (q12Point 5) (q12Point 10) *
      Equiv.swap (q12Point 10) (q12Point 8)) *
    (Equiv.swap (q12Point 6) (q12Point 11) *
      Equiv.swap (q12Point 11) (q12Point 7))

def classY2 : Equiv.Perm Q12 :=
  (Equiv.swap (q12Point 1) (q12Point 4) *
      Equiv.swap (q12Point 4) (q12Point 7) *
      Equiv.swap (q12Point 7) (q12Point 10)) *
    (Equiv.swap (q12Point 2) (q12Point 9) *
      Equiv.swap (q12Point 9) (q12Point 6) *
      Equiv.swap (q12Point 6) (q12Point 5)) *
    (Equiv.swap (q12Point 3) (q12Point 12) *
      Equiv.swap (q12Point 12) (q12Point 11) *
      Equiv.swap (q12Point 11) (q12Point 8))

def classX3 : Equiv.Perm Q12 :=
  (Equiv.swap (q12Point 1) (q12Point 2) *
      Equiv.swap (q12Point 2) (q12Point 3)) *
    (Equiv.swap (q12Point 4) (q12Point 8) *
      Equiv.swap (q12Point 8) (q12Point 11)) *
    (Equiv.swap (q12Point 5) (q12Point 7) *
      Equiv.swap (q12Point 7) (q12Point 12)) *
    (Equiv.swap (q12Point 6) (q12Point 9) *
      Equiv.swap (q12Point 9) (q12Point 10))

def classY3 : Equiv.Perm Q12 :=
  (Equiv.swap (q12Point 1) (q12Point 4) *
      Equiv.swap (q12Point 4) (q12Point 7) *
      Equiv.swap (q12Point 7) (q12Point 10)) *
    (Equiv.swap (q12Point 2) (q12Point 11) *
      Equiv.swap (q12Point 11) (q12Point 12) *
      Equiv.swap (q12Point 12) (q12Point 9)) *
    (Equiv.swap (q12Point 3) (q12Point 8) *
      Equiv.swap (q12Point 8) (q12Point 5) *
      Equiv.swap (q12Point 5) (q12Point 6))

def classX : Fin 3 → Equiv.Perm Q12 :=
  ![classX1, classX2, classX3]

def classY : Fin 3 → Equiv.Perm Q12 :=
  ![classY1, classY2, classY3]

def regularQ12Copy (i : Fin 3) : Subgroup (Equiv.Perm Q12) :=
  Subgroup.closure {classX i, classY i}

def regularQ12Action (i : Fin 3) (h : Q12) : Equiv.Perm Q12 :=
  classY i ^ h.2.val * classX i ^ h.1.val

def regularQ12 (i : Fin 3) : Prop :=
  Nat.card (regularQ12Copy i) = 12 ∧
    (∀ g : Equiv.Perm Q12, g ∈ regularQ12Copy i →
      ∃ h : Q12, g = regularQ12Action i h) ∧
      (∀ v w : Q12, ∃! h : Q12, regularQ12Action i h v = w) ∧
        (∀ h k : Q12,
          regularQ12Action i (q12Mul h k) =
            regularQ12Action i k * regularQ12Action i h) ∧
          (∀ h : Q12, regularQ12Action i h ∈ regularQ12Copy i)

def conjugatesWithin {α : Type*}
    (A R T : Subgroup (Equiv.Perm α)) : Prop :=
  ∃ g : A, ∀ r : Equiv.Perm α,
    r ∈ R ↔ (g : Equiv.Perm α)⁻¹ * r * (g : Equiv.Perm α) ∈ T

def selectedCrossClassPair
    (A : Subgroup (Equiv.Perm Q12)) (i j : Fin 3) : Prop :=
  i ≠ j ∧ regularQ12 i ∧ regularQ12 j ∧
    regularQ12Copy i ≤ A ∧ regularQ12Copy j ≤ A ∧
      ¬conjugatesWithin A (regularQ12Copy i) (regularQ12Copy j)

def block (v : Q12) : Set G156 :=
  {x | x.2 = v}

def displayedLiftFormula (i : Fin 3) (a : ZMod 13) (h : Q12)
    (f : Equiv.Perm G156) : Prop :=
  ∀ c : ZMod 13, ∀ v : Q12,
    f (c, v) = (q156Chi h * (c + a), regularQ12Action i h v)

def displayedLiftSet (i : Fin 3) : Set (Equiv.Perm G156) :=
  {f | ∃ a : ZMod 13, ∃ h : Q12, displayedLiftFormula i a h f}

def displayedLiftSubgroup (i : Fin 3) : Subgroup (Equiv.Perm G156) :=
  Subgroup.closure (displayedLiftSet i)

def regularQ156Lift (i : Fin 3) : Prop :=
  (∀ a : ZMod 13, ∀ h : Q12,
    ∃! f : Equiv.Perm G156, displayedLiftFormula i a h f) ∧
    (∀ f : Equiv.Perm G156, f ∈ displayedLiftSet i →
      relationAutomorphism recognitionAdj f) ∧
    (∀ f : Equiv.Perm G156,
      f ∈ displayedLiftSet i ↔ f ∈ displayedLiftSubgroup i) ∧
    Nonempty (displayedLiftSubgroup i ≃* QuaternionGroup 39) ∧
    (∀ x y : G156, ∃! f : Equiv.Perm G156,
      f ∈ displayedLiftSet i ∧ f x = y) ∧
    Set.ncard (displayedLiftSet i) = 156 ∧
    (∀ f : Equiv.Perm G156, f ∈ displayedLiftSet i →
      ∃ a : ZMod 13, ∃ h : Q12,
        displayedLiftFormula i a h f ∧
          ∀ v : Q12, Set.image f (block v) =
            block (regularQ12Action i h v))

def exceptionalLiftPair
    (A : Subgroup (Equiv.Perm Q12)) (i j : Fin 3) : Prop :=
  selectedCrossClassPair A i j ∧
    regularQ156Lift i ∧ regularQ156Lift j

def claim41720 : Prop :=
  Nat.card exceptionalAmbient127 = 288 ∧
    exceptionalLiftPair exceptionalAmbient127 0 1 ∧
      Nat.card exceptionalAmbient204 = 1152 ∧
        exceptionalLiftPair exceptionalAmbient204 0 1 ∧
          exceptionalLiftPair exceptionalAmbient204 0 2 ∧
            exceptionalLiftPair exceptionalAmbient204 1 2

def rho : Equiv.Perm (ZMod 13) :=
  Equiv.swap 0 1

def nu : Equiv.Perm G156 :=
  Equiv.prodCongr rho (Equiv.refl Q12)

def commonBlockPreserving (f : Equiv.Perm G156) : Prop :=
  ∀ v : Q12, Set.image f (block v) = block v

def affineOverF13 (f : ZMod 13 → ZMod 13) : Prop :=
  ∃ a b : ZMod 13, ∀ x : ZMod 13, f x = a * x + b

def claim41721 : Prop :=
  relationAutomorphism recognitionAdj nu ∧
    commonBlockPreserving nu ∧
    (∀ c : ZMod 13, ∀ v : Q12,
      coordinateChart (nu (coordinateChart (c, v))) =
        (q156Chi v * rho (q156Chi v * c), v)) ∧
    (∀ v : Q12,
      ¬affineOverF13 (fun x : ZMod 13 =>
        q156Chi v * rho (q156Chi v * x)))


/-- The order-three quotient switch used only in the zero component. -/
def q12SwitchCycle (a b c : Q12) : Equiv.Perm Q12 :=
  (Equiv.swap b c).trans (Equiv.swap a b)

def q12Sigma : Equiv.Perm Q12 :=
  (q12SwitchCycle (1, 1) (1, 3) (2, 2)).trans
    (q12SwitchCycle (2, 1) (1, 2) (2, 3))

def componentLocalSwitch (x : G156) : G156 :=
  if x.1 = 0 then (0, q12Sigma x.2) else x

def relationAutomorphismFunction {α : Type*}
    (r : α → α → Prop) (f : α → α) : Prop :=
  Function.Bijective f ∧ ∀ x y, r x y ↔ r (f x) (f y)

def commonBlockPartition : Set (Set G156) :=
  Set.range block

def breaksCommonBlockPartition (f : G156 → G156) : Prop :=
  ∃ v v₁ v₂ : Q12,
    v₁ ≠ v₂ ∧
      (∃ x, x ∈ f '' block v ∧ x.2 = v₁) ∧
      (∃ x, x ∈ f '' block v ∧ x.2 = v₂) ∧
      f '' block v ∉ commonBlockPartition

/-- Claim 41722: a component-local order-three quotient automorphism is a
full automorphism of the recognition graph and breaks the common C₁₃ blocks. -/
def claim41722 : Prop :=
  orderOf q12Sigma = 3 ∧
    relationAutomorphism quotientAdj q12Sigma ∧
      relationAutomorphismFunction recognitionAdj componentLocalSwitch ∧
        breaksCommonBlockPartition componentLocalSwitch

end MathlibPlus.Open.GraphTheory.Q156RecognitionClaims41718_41722
