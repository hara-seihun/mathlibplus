import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Order72ComponentShadowClaim61344

noncomputable section

abbrev A := Fin 3 → ZMod 2
abbrev B := Fin 2 → ZMod 3
abbrev G := A × B

/-- The lexicographic enumeration of `F_3^2` used by the displayed table. -/
def bOfIndex (i : Fin 9) : B :=
  ![((i.val / 3 : ℕ) : ZMod 3), ((i.val % 3 : ℕ) : ZMod 3)]

/-- The nine entries of the displayed nonlinear base permutation. -/
def sigmaOrder (i : Fin 9) : Fin 9 :=
  if i.val = 0 then (0 : Fin 9) else
    if i.val = 1 then (4 : Fin 9) else
      if i.val = 2 then (8 : Fin 9) else
        if i.val = 3 then (5 : Fin 9) else
          if i.val = 4 then (6 : Fin 9) else
            if i.val = 5 then (1 : Fin 9) else
              if i.val = 6 then (2 : Fin 9) else
                if i.val = 7 then (7 : Fin 9) else (3 : Fin 9)

def sigmaValues (b : B) : B :=
  bOfIndex
    (if b = bOfIndex 0 then (0 : Fin 9) else
      if b = bOfIndex 1 then (4 : Fin 9) else
        if b = bOfIndex 2 then (8 : Fin 9) else
          if b = bOfIndex 3 then (5 : Fin 9) else
            if b = bOfIndex 4 then (6 : Fin 9) else
              if b = bOfIndex 5 then (1 : Fin 9) else
                if b = bOfIndex 6 then (2 : Fin 9) else
                  if b = bOfIndex 7 then (7 : Fin 9) else (3 : Fin 9))

/-- The displayed nine translation vectors, in the same lexicographic order. -/
def cValues (i : Fin 9) : A :=
  if i.val = 0 then ![0, 0, 0] else
    if i.val = 1 then ![1, 0, 0] else
      if i.val = 2 then ![0, 1, 0] else
        if i.val = 3 then ![0, 0, 1] else
          if i.val = 4 then ![1, 1, 0] else
            if i.val = 5 then ![1, 0, 1] else
              if i.val = 6 then ![0, 1, 1] else
                if i.val = 7 then ![1, 1, 1] else ![1, 0, 0]

def cValuesOnB (b : B) : A :=
  cValues
    (if b = bOfIndex 0 then (0 : Fin 9) else
      if b = bOfIndex 1 then (1 : Fin 9) else
        if b = bOfIndex 2 then (2 : Fin 9) else
          if b = bOfIndex 3 then (3 : Fin 9) else
            if b = bOfIndex 4 then (4 : Fin 9) else
              if b = bOfIndex 5 then (5 : Fin 9) else
                if b = bOfIndex 6 then (6 : Fin 9) else
                  if b = bOfIndex 7 then (7 : Fin 9) else (8 : Fin 9))

/-- The pointed permutation from the admitted order-72 presentation. -/
def displayedPermutation : G → G :=
  fun g => (g.1 + cValuesOnB g.2, sigmaValues g.2)

/-- The matrix `((0,1),(1,1))` over `F_3`. -/
def displayedMatrix : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  fun i j =>
    if i = 0 then
      if j = 0 then 0 else 1
    else
      1

/-- The displayed linear shadow on `F_2^3 × F_3^2`. -/
def displayedAlpha : G → G :=
  fun g => (g.1, displayedMatrix.mulVec g.2)

/-- The inverse atom attached to a nonzero group element. -/
def inverseAtom (v : G) : Set G :=
  {v, -v}

/-- The 39 inverse atoms in `G \ {0}`. -/
def inverseAtomSet : Set (Set G) :=
  {S | ∃ v : G, v ≠ 0 ∧ S = inverseAtom v}

/-- A vertex of the bipartite inverse-atom incidence graph. -/
abbrev Atom := {S : Set G // S ∈ inverseAtomSet}
abbrev Vertex := Bool × Atom

/-- The incidence condition for a left atom and a right atom. -/
def atomIncidence (left right : Atom) : Prop :=
  ∃ x : G, ∃ d : G,
    d ∈ left.1 ∧ displayedPermutation (x + d) - displayedPermutation x ∈ right.1

/-- The undirected bipartite incidence relation. -/
def incidenceEdge (u v : Vertex) : Prop :=
  (u.1 = false ∧ v.1 = true ∧ atomIncidence u.2 v.2) ∨
    (u.1 = true ∧ v.1 = false ∧ atomIncidence v.2 u.2)

/-- Connectedness in the incidence graph. -/
def incidenceConnected (u v : Vertex) : Prop :=
  Relation.EqvGen incidenceEdge u v

def incidenceComponent (u : Vertex) : Set Vertex :=
  {v | incidenceConnected u v}

def incidenceComponents : Set (Set Vertex) :=
  Set.range incidenceComponent

def componentLeft (C : Set Vertex) : Set Atom :=
  {a | (false, a) ∈ C}

def componentRight (C : Set Vertex) : Set Atom :=
  {a | (true, a) ∈ C}

def componentSizePair (C : Set Vertex) : ℕ × ℕ :=
  (Set.ncard (componentLeft C), Set.ncard (componentRight C))

/-- The exact nine-component size pattern `(8,8),(24,24),(1,1)^7`. -/
def componentEnumeration (components : Fin 9 → Set Vertex) : Prop :=
  Function.Injective components ∧
    Set.range components = incidenceComponents ∧
      ∃ i8 i24 : Fin 9,
        i8 ≠ i24 ∧
          ∀ i : Fin 9,
            componentSizePair (components i) =
              if i = i8 then (8, 8) else
                if i = i24 then (24, 24) else (1, 1)

/-- A group element map sends one inverse atom onto another. -/
def mapsAtom (alpha : G → G) (a b : Atom) : Prop :=
  Set.image alpha a.1 = b.1

/-- The componentwise assertion that `alpha` maps left atoms onto right atoms. -/
def alphaMapsComponent (alpha : G → G) (C : Set Vertex) : Prop :=
  {b : Atom |
      ∃ a : Atom, a ∈ componentLeft C ∧ mapsAtom alpha a b} =
    componentRight C

/-- The union of the left inverse atoms selected by a component-index set. -/
def leftConnectionUnion (components : Fin 9 → Set Vertex)
    (J : Set (Fin 9)) : Set G :=
  {v | ∃ i : Fin 9, i ∈ J ∧
    ∃ a : Atom, a ∈ componentLeft (components i) ∧ v ∈ a.1}

/-- The corresponding union of right inverse atoms. -/
def rightConnectionUnion (components : Fin 9 → Set Vertex)
    (J : Set (Fin 9)) : Set G :=
  {v | ∃ i : Fin 9, i ∈ J ∧
    ∃ a : Atom, a ∈ componentRight (components i) ∧ v ∈ a.1}

/-- Ordinary undirected Cayley adjacency on the additive order-72 carrier. -/
def cayleyAdjacency (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- A bijective Cayley graph isomorphism for the displayed presentation. -/
def displayedGraphIsomorphism
    (components : Fin 9 → Set Vertex) (J : Set (Fin 9)) : Prop :=
  Function.Bijective displayedPermutation ∧
    ∀ x y : G,
      cayleyAdjacency (leftConnectionUnion components J) x y ↔
        cayleyAdjacency (rightConnectionUnion components J)
          (displayedPermutation x) (displayedPermutation y)

/-- The displayed linear map is a group automorphism of the additive carrier. -/
def displayedGroupAutomorphism : Prop :=
  Function.Bijective displayedAlpha ∧
    displayedAlpha 0 = 0 ∧
      ∀ x y : G, displayedAlpha (x + y) =
        displayedAlpha x + displayedAlpha y

/-- Claim 61344: the exact nine-component incidence family and its common
linear shadow for every independently selected finite tuple. -/
def claim61344 : Prop :=
  Set.ncard inverseAtomSet = 39 ∧
    displayedPermutation 0 = 0 ∧
      Function.Bijective displayedPermutation ∧
        displayedGroupAutomorphism ∧
          ∃ components : Fin 9 → Set Vertex,
            componentEnumeration components ∧
              (∀ i : Fin 9, alphaMapsComponent displayedAlpha
                (components i)) ∧
                (∀ J : Set (Fin 9),
                  displayedGraphIsomorphism components J ∧
                    Set.image displayedAlpha
                      (leftConnectionUnion components J) =
                      rightConnectionUnion components J) ∧
                  (∀ k : ℕ, ∀ selections : Fin k → Set (Fin 9),
                    ∀ i : Fin k,
                      Set.image displayedAlpha
                          (leftConnectionUnion components (selections i)) =
                        rightConnectionUnion components (selections i) ∧
                        ∀ x y : G,
                          cayleyAdjacency
                              (leftConnectionUnion components (selections i))
                              x y ↔
                            cayleyAdjacency
                              (rightConnectionUnion components (selections i))
                              (displayedAlpha x) (displayedAlpha y))

end

end MathlibPlus.Open.ResearchFormalization.Order72ComponentShadowClaim61344
