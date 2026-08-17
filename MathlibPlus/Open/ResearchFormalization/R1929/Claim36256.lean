import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1929

abbrev SquareMismatchG := ZMod 4 × (Fin 3 → ZMod 3)
abbrev SquareMismatchV := Fin 3 → ZMod 3

def squareMismatchConnectionSet : Set SquareMismatchG :=
  {g | g.2 ≠ 0}

def squareMismatchGraph : SimpleGraph SquareMismatchG :=
  SimpleGraph.fromRel (fun x y : SquareMismatchG =>
    y - x ∈ squareMismatchConnectionSet)

def squarePermutation (a : ZMod 4) : ZMod 4 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 3 else 2

def squareMismatchConjugator (x : SquareMismatchG) : SquareMismatchG :=
  if x.2 = 0 then (squarePermutation x.1, 0) else x

def squareMismatchTranslation (g x : SquareMismatchG) : SquareMismatchG :=
  g + x

def squareMismatchUnitVector (j : Fin 3) : SquareMismatchV :=
  fun i => if i = j then 1 else 0

def squareMismatchGeneratorElements : Set SquareMismatchG :=
  {(1, 0)} ∪ {g | ∃ j : Fin 3, g = (0, squareMismatchUnitVector j)}

def squareMismatchGeneratorsGenerate : Prop :=
  AddSubgroup.closure squareMismatchGeneratorElements = ⊤

def squareMismatchRGenerator : SquareMismatchG → SquareMismatchG :=
  squareMismatchTranslation (1, 0)

def squareMismatchCoordinateGenerator (j : Fin 3) :
    SquareMismatchG → SquareMismatchG :=
  squareMismatchTranslation (0, squareMismatchUnitVector j)

def squareMismatchTranslationCopy : Set (SquareMismatchG → SquareMismatchG) :=
  {t | ∃ g : SquareMismatchG, ∀ x : SquareMismatchG,
    t x = squareMismatchTranslation g x}

def squareMismatchCompose (f g : SquareMismatchG → SquareMismatchG) :
    SquareMismatchG → SquareMismatchG :=
  fun x => f (g x)

def squareMismatchRawSubgroup (H : Set (SquareMismatchG → SquareMismatchG)) : Prop :=
  (fun x => x) ∈ H ∧
    (∀ f g, f ∈ H → g ∈ H → squareMismatchCompose f g ∈ H) ∧
    (∀ f, f ∈ H → Function.invFun f ∈ H)

def squareMismatchConjugateCopy
    (f : SquareMismatchG → SquareMismatchG)
    (X : Set (SquareMismatchG → SquareMismatchG)) :
    Set (SquareMismatchG → SquareMismatchG) :=
  {t | ∃ q, q ∈ X ∧ ∀ x,
    t x = Function.invFun f (q (f x))}

def squareMismatchRegularCopy
    (X : Set (SquareMismatchG → SquareMismatchG)) : Prop :=
  (∀ t, t ∈ X → Function.Bijective t) ∧
    squareMismatchRawSubgroup X ∧
    (∀ x y : SquareMismatchG, ∃! t,
      t ∈ X ∧ t x = y)

def squareMismatchGraphAutomorphismCopy
    (X : Set (SquareMismatchG → SquareMismatchG)) : Prop :=
  ∀ t, t ∈ X → Function.Bijective t ∧
    (∀ x y : SquareMismatchG,
      squareMismatchGraph.Adj x y ↔
        squareMismatchGraph.Adj (t x) (t y))

def squareMismatchPartition (P : Set (Set SquareMismatchG)) : Prop :=
  (∀ B, B ∈ P → B.Nonempty) ∧
    (∀ x : SquareMismatchG, ∃! B, B ∈ P ∧ x ∈ B)

def squareMismatchOrbit
    (H : Set (SquareMismatchG → SquareMismatchG))
    (x : SquareMismatchG) : Set SquareMismatchG :=
  {y | ∃ h, h ∈ H ∧ y = h x}

def squareMismatchCosetBlockSystem
    (X : Set (SquareMismatchG → SquareMismatchG))
    (P : Set (Set SquareMismatchG)) : Prop :=
  squareMismatchPartition P ∧
    ∃ H : Set (SquareMismatchG → SquareMismatchG),
      squareMismatchRawSubgroup H ∧ H ⊆ X ∧
        (∀ B, B ∈ P → ∃ x,
          B = squareMismatchOrbit H x) ∧
        (∀ x : SquareMismatchG, ∃ B, B ∈ P ∧
          B = squareMismatchOrbit H x)

def squareMismatchCommonCosetRefinement (k : ℕ) : Prop :=
  ∃ P : Set (Set SquareMismatchG),
    squareMismatchCosetBlockSystem squareMismatchTranslationCopy P ∧
      squareMismatchCosetBlockSystem
        (squareMismatchConjugateCopy squareMismatchConjugator
          squareMismatchTranslationCopy) P ∧
      (∀ B, B ∈ P → Set.ncard B = k)

def squareMismatchFiberBlocks : Set (Set SquareMismatchG) :=
  {B | ∃ v : SquareMismatchV, B = {x | x.2 = v}}

def squareMismatchLocalBlockConclusion : Prop :=
  squareMismatchCommonCosetRefinement 4 ∧
    squareMismatchCosetBlockSystem squareMismatchTranslationCopy
      squareMismatchFiberBlocks ∧
    squareMismatchCosetBlockSystem
      (squareMismatchConjugateCopy squareMismatchConjugator
        squareMismatchTranslationCopy) squareMismatchFiberBlocks ∧
    (∀ B, B ∈ squareMismatchFiberBlocks → Set.ncard B = 4) ∧
    ¬ squareMismatchCommonCosetRefinement 2 ∧
    ¬ squareMismatchCommonCosetRefinement 3

/-- The explicit order-108 graph witness, including the independent subgroup
coset blocks for the two regular copies. -/
def graphRealizableSquareMismatchedBranch_claim36256 : Prop :=
  let R := squareMismatchTranslationCopy
  let T := squareMismatchConjugateCopy squareMismatchConjugator R
  (0, 0) ∉ squareMismatchConnectionSet ∧
    (∀ g : SquareMismatchG, g ∈ squareMismatchConnectionSet →
      -g ∈ squareMismatchConnectionSet) ∧
    Fintype.card SquareMismatchG = 108 ∧
    Fintype.card SquareMismatchV = 27 ∧
    squareMismatchGraph.IsCompleteMultipartite ∧
    (∀ x y : SquareMismatchG,
      squareMismatchGraph.Adj x y ↔ x.2 ≠ y.2) ∧
    (∀ v : SquareMismatchV,
      Set.ncard {x : SquareMismatchG | x.2 = v} = 4) ∧
    Set.ncard squareMismatchGraph.edgeSet = 5616 ∧
    (∀ x : SquareMismatchG,
      Set.ncard (squareMismatchGraph.neighborSet x) = 104) ∧
    squareMismatchGraph.Connected ∧
    (¬ ∀ x y : SquareMismatchG,
      x ≠ y → squareMismatchGraph.Adj x y) ∧
    squareMismatchRegularCopy R ∧
    squareMismatchRegularCopy T ∧
    squareMismatchGraphAutomorphismCopy R ∧
    squareMismatchGraphAutomorphismCopy T ∧
    squareMismatchRGenerator ∈ R ∧
    (∀ j : Fin 3, squareMismatchCoordinateGenerator j ∈ R) ∧
    squareMismatchGeneratorsGenerate ∧
    Function.Bijective squareMismatchConjugator ∧
    (∀ x y : SquareMismatchG,
      squareMismatchGraph.Adj x y ↔
        squareMismatchGraph.Adj
          (squareMismatchConjugator x) (squareMismatchConjugator y)) ∧
    T = squareMismatchConjugateCopy squareMismatchConjugator R ∧
    squareMismatchLocalBlockConclusion ∧
    squareMismatchCommonCosetRefinement 4

end MathlibPlus.Open.ResearchFormalization.R1929
