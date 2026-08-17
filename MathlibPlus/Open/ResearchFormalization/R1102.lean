import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1102

noncomputable section

abbrev F7 := ZMod 7
abbrev A7 := F7 × F7
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) F7

/-- The two factor connection sets on the additive cyclic group of order seven. -/
def factorSet1 : Set F7 := {z | z = 1 ∨ z = -1}

def factorSet2 : Set F7 :=
  {z | z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2}

/-- The two connection sets on the coordinate square. -/
def coordinateSet1 : Set A7 :=
  {z | z.1 = 0 ∧ z.2 ∈ factorSet1}

def coordinateSet2 : Set A7 :=
  {z | z.1 = 0 ∧ z.2 ∈ factorSet2}

/-- The loopless additive Cayley relation used for all four graph representatives. -/
def cayleyAdj {V : Type*} [AddGroup V] (S : Set V) (x y : V) : Prop :=
  x ≠ y ∧ y - x ∈ S

def factorAdj1 : F7 → F7 → Prop := cayleyAdj factorSet1

def factorAdj2 : F7 → F7 → Prop := cayleyAdj factorSet2

def graph1 : A7 → A7 → Prop := cayleyAdj coordinateSet1

def graph2 : A7 → A7 → Prop := cayleyAdj coordinateSet2

/-- Off-diagonal graph complement. -/
def graphComplement {V : Type*} (adj : V → V → Prop) (x y : V) : Prop :=
  x ≠ y ∧ ¬adj x y

/-- The two displayed matrices, acting on column coordinates in `F₇²`. -/
def m17791 : Matrix2 :=
  fun i j =>
    if i = 0 then
      if j = 0 then 0 else 2
    else if j = 0 then 1 else 4

def m17792 : Matrix2 :=
  fun i j =>
    if i = 0 then
      if j = 0 then 0 else 3
    else if j = 0 then 1 else 6

/-- Matrix action on the coordinate square. -/
def matrixAction (M : Matrix2) (x : A7) : A7 :=
  (M 0 0 * x.1 + M 0 1 * x.2,
    M 1 0 * x.1 + M 1 1 * x.2)

/-- The relation obtained by applying a specified linear map to both endpoints. -/
def linearImageAdj (M : Matrix2) (adj : A7 → A7 → Prop)
    (u v : A7) : Prop :=
  ∃ x y, adj x y ∧ matrixAction M x = u ∧ matrixAction M y = v

def graph17791 : A7 → A7 → Prop :=
  linearImageAdj m17791 (graphComplement graph2)

def graph17792 : A7 → A7 → Prop :=
  linearImageAdj m17792 (graphComplement graph1)

/-- The degree of a vertex in a finite relation. -/
noncomputable def degree {V : Type*} [Fintype V]
    (adj : V → V → Prop) (x : V) : ℕ :=
  Nat.card {y : V // adj x y}

/-- The seven coordinate fibres and their displayed linear images. -/
def fiber (i : F7) : Set A7 := {x | x.1 = i}

def normalizedFiber (M : Matrix2) (i : F7) : Set A7 :=
  matrixAction M '' fiber i

/-- Exact decomposition into seven factor copies. -/
def sevenFactorDecomposition (adj : A7 → A7 → Prop)
    (S : Set F7) : Prop :=
  ∀ x y : A7,
    adj x y ↔ x.1 = y.1 ∧ cayleyAdj S x.2 y.2

/-- Reachability component of a vertex for a relation. -/
def componentOf {V : Type*} (adj : V → V → Prop) (x : V) : Set V :=
  {y | Relation.ReflTransGen adj x y}

/-- A named seven-block system is exactly the component partition. -/
def sevenComponentSystem (adj : A7 → A7 → Prop)
    (blocks : F7 → Set A7) : Prop :=
  (∀ x : A7, ∃ i : F7, x ∈ blocks i) ∧
    (∀ i j : F7, i ≠ j → Disjoint (blocks i) (blocks j)) ∧
      (∀ i : F7, ∀ x ∈ blocks i, componentOf adj x = blocks i)

/-- Every graph automorphism permutes the named seven-block system. -/
def permutesSevenSystem (adj : A7 → A7 → Prop)
    (blocks : F7 → Set A7) : Prop :=
  ∀ g : Equiv.Perm A7, (∀ x y, adj x y ↔ adj (g x) (g y)) →
    ∀ i : F7, ∃ j : F7, g '' blocks i = blocks j

/-- Exact coordinate models, component copies, and valencies for the four retained graphs. -/
def claim_28905 : Prop :=
  (∀ x y : A7, graph1 x y ↔ cayleyAdj coordinateSet1 x y) ∧
    (∀ x y : A7, graph2 x y ↔ cayleyAdj coordinateSet2 x y) ∧
    sevenFactorDecomposition graph1 factorSet1 ∧
    sevenFactorDecomposition graph2 factorSet2 ∧
    (∀ u v : A7,
      graph17791 u v ↔
        linearImageAdj m17791 (graphComplement graph2) u v) ∧
    (∀ u v : A7,
      graph17792 u v ↔
        linearImageAdj m17792 (graphComplement graph1) u v) ∧
    (∀ x : A7, degree graph1 x = 2) ∧
    (∀ x : A7, degree graph2 x = 4) ∧
    (∀ x : A7, degree graph17791 x = 44) ∧
    (∀ x : A7, degree graph17792 x = 46)

/-- Invertibility and the normalization action on the two complement representatives. -/
def matrixInvertible (M : Matrix2) : Prop := M.det ≠ 0

def normalizes17791 (M : Matrix2) : Prop :=
  matrixInvertible M ∧
    ∀ u v : A7,
      linearImageAdj M (graphComplement graph2) u v ↔ graph17791 u v

def normalizes17792 (M : Matrix2) : Prop :=
  matrixInvertible M ∧
    ∀ u v : A7,
      linearImageAdj M (graphComplement graph1) u v ↔ graph17792 u v

noncomputable def normalizerCard17791 : ℕ :=
  Nat.card {M : Matrix2 // normalizes17791 M}

noncomputable def normalizerCard17792 : ℕ :=
  Nat.card {M : Matrix2 // normalizes17792 M}

/-- Row-major lexicographic order on matrices, using least residues in `F₇`. -/
def matrixLexLe (M N : Matrix2) : Prop :=
  ZMod.val (M 0 0) < ZMod.val (N 0 0) ∨
    (M 0 0 = N 0 0 ∧
      (ZMod.val (M 0 1) < ZMod.val (N 0 1) ∨
        (M 0 1 = N 0 1 ∧
          (ZMod.val (M 1 0) < ZMod.val (N 1 0) ∨
            (M 1 0 = N 1 0 ∧
              ZMod.val (M 1 1) ≤ ZMod.val (N 1 1))))))

/-- The displayed matrices are the lexicographically first normalizers, and each
normalizer fibre has the stated size. -/
def claim_28906 : Prop :=
  (m17791 0 0 = (0 : F7) ∧ m17791 0 1 = (2 : F7) ∧
      m17791 1 0 = (1 : F7) ∧ m17791 1 1 = (4 : F7)) ∧
    (m17792 0 0 = (0 : F7) ∧ m17792 0 1 = (3 : F7) ∧
      m17792 1 0 = (1 : F7) ∧ m17792 1 1 = (6 : F7)) ∧
    normalizes17791 m17791 ∧ normalizes17792 m17792 ∧
    normalizerCard17791 = 84 ∧ normalizerCard17792 = 84 ∧
    (∀ M : Matrix2, normalizes17791 M → matrixLexLe m17791 M) ∧
    (∀ M : Matrix2, normalizes17792 M → matrixLexLe m17792 M)

/-- The affine dihedral permutations of the two seven-cycles.  The choice of
sign is global, not pointwise. -/
def dihedralForm (g : Equiv.Perm F7) : Prop :=
  ∃ a : F7,
    ((∀ x : F7, g x = x + a) ∨
      (∀ x : F7, g x = -x + a))

def connectedRelation {V : Type*} (adj : V → V → Prop) : Prop :=
  ∀ x y : V, Relation.ReflTransGen adj x y

/-- Both retained cyclic factors are connected and have precisely the affine
`D₁₄` automorphisms. -/
def claim_28907 : Prop :=
  connectedRelation factorAdj1 ∧
    connectedRelation factorAdj2 ∧
    (∀ g : Equiv.Perm F7,
      (∀ x y : F7, factorAdj1 x y ↔ factorAdj1 (g x) (g y)) ↔
        dihedralForm g) ∧
    (∀ g : Equiv.Perm F7,
      (∀ x y : F7, factorAdj2 x y ↔ factorAdj2 (g x) (g y)) ↔
        dihedralForm g) ∧
    Nat.card {g : Equiv.Perm F7 // dihedralForm g} = 14

/-- The intrinsic component systems, including the automorphism permutation
conclusion for all four graph representatives. -/
def claim_28908 : Prop :=
  sevenComponentSystem graph1 (fiber) ∧
    sevenComponentSystem graph2 (fiber) ∧
    sevenComponentSystem (graphComplement graph17791)
      (normalizedFiber m17791) ∧
    sevenComponentSystem (graphComplement graph17792)
      (normalizedFiber m17792) ∧
    permutesSevenSystem graph1 fiber ∧
    permutesSevenSystem graph2 fiber ∧
    permutesSevenSystem graph17791 (normalizedFiber m17791) ∧
    permutesSevenSystem graph17792 (normalizedFiber m17792)

end

end MathlibPlus.Open.ResearchFormalization.R1102
