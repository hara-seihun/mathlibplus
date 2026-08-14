import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev F5Six := Fin 6 → ZMod 5
abbrev CycleComponents := Fin 3125
abbrev CycleVertex := CycleComponents × ZMod 5
abbrev CycleMatrix := Matrix CycleVertex CycleVertex ℚ

/-- The sixth standard coordinate vector in `𝔽₅⁶`. -/
def sixthBasis : F5Six := fun k => if k = (5 : Fin 6) then 1 else 0

/-- The edge relation of the Cayley graph with connection set `±e₆`. -/
def gammaZeroAdj (x y : F5Six) : Prop :=
  y - x = sixthBasis ∨ y - x = -sixthBasis

/-- The disjoint union of 3125 five-cycles. -/
def cycleAdj (x y : CycleVertex) : Prop :=
  x.1 = y.1 ∧ (y.2 - x.2 = 1 ∨ y.2 - x.2 = -1)

def relationAutomorphism {α : Type*} (adj : α → α → Prop) (q : Equiv.Perm α) : Prop :=
  ∀ x y, adj x y ↔ adj (q x) (q y)

def relationEquiv {α β : Type*} (adjα : α → α → Prop) (adjβ : β → β → Prop)
    (e : α ≃ β) : Prop :=
  ∀ x y, adjα x y ↔ adjβ (e x) (e y)

/-- The usual explicit action of `D₁₀ wr S₃₁₂₅` on the cycles. -/
def dihedralWreathMember (q : Equiv.Perm CycleVertex) : Prop :=
  ∃ σ : Equiv.Perm CycleComponents,
    ∀ b : CycleComponents,
      ∃ ε : Fin 2, ∃ r : ZMod 5,
        ∀ x : ZMod 5,
          q (b, x) = (σ b, (if ε = 0 then x else -x) + r)

/-- The four relation matrices of the actual rank-four closure. -/
def cycleIdentity : CycleMatrix := fun x y => if x = y then 1 else 0
def cycleAllOnes : CycleMatrix := fun _ _ => 1
def cycleA : CycleMatrix := fun x y =>
  if x.1 = y.1 ∧ (y.2 - x.2 = 1 ∨ y.2 - x.2 = -1) then 1 else 0
def cycleB : CycleMatrix := fun x y =>
  if x.1 = y.1 ∧ (y.2 - x.2 = 2 ∨ y.2 - x.2 = -2) then 1 else 0
def cycleC : CycleMatrix := fun x y => if x.1 ≠ y.1 then 1 else 0

def matrixHadamard (X Y : CycleMatrix) : CycleMatrix := fun i j => X i j * Y i j

def coherentMatrixSet (W : Set CycleMatrix) : Prop :=
  (0 : CycleMatrix) ∈ W ∧
    (∀ {X Y}, X ∈ W → Y ∈ W → X + Y ∈ W) ∧
    (∀ (r : ℚ) {X}, X ∈ W → r • X ∈ W) ∧
    (∀ {X Y}, X ∈ W → Y ∈ W → X * Y ∈ W) ∧
    (∀ {X Y}, X ∈ W → Y ∈ W → matrixHadamard X Y ∈ W) ∧
    (∀ {X}, X ∈ W → X.transpose ∈ W)

def actualCoherentClosure (A : CycleMatrix) : Set CycleMatrix :=
  ⋂₀ {W : Set CycleMatrix |
    coherentMatrixSet W ∧ cycleIdentity ∈ W ∧ cycleAllOnes ∈ W ∧ A ∈ W}

def rankFourSpan : Set CycleMatrix :=
  (Submodule.span ℚ ({cycleIdentity, cycleA, cycleB, cycleC} : Set CycleMatrix) : Set CycleMatrix)

/-- Claim 28118: the concrete graph, its full wreath automorphism group, and its
rank-four actual coherent closure. -/
def graphUnionClosureRankFour : Prop :=
  (∃ e : F5Six ≃ CycleVertex, relationEquiv gammaZeroAdj cycleAdj e) ∧
    (∀ q : Equiv.Perm CycleVertex,
      relationAutomorphism cycleAdj q ↔ dihedralWreathMember q) ∧
    actualCoherentClosure cycleA = rankFourSpan ∧
    Module.finrank ℚ (Submodule.span ℚ (actualCoherentClosure cycleA)) = 4

/-- Claim 28119: multiplication in the four-dimensional closure. -/
def rankFourClosureMultiplicationTable : Prop :=
  cycleA * cycleA = (2 : ℚ) • cycleIdentity + cycleB ∧
    cycleB * cycleB = (2 : ℚ) • cycleIdentity + cycleA ∧
    cycleA * cycleB = cycleA + cycleB ∧
    cycleA * cycleC = (2 : ℚ) • cycleC ∧
    cycleB * cycleC = (2 : ℚ) • cycleC ∧
    cycleC * cycleC =
      ((5 : ℚ) * 3124) • (cycleIdentity + cycleA + cycleB) +
        ((5 : ℚ) * 3123) • cycleC ∧
    actualCoherentClosure cycleA = rankFourSpan

end MathlibPlus.Open.ResearchFormalization
