import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

section TernaryCap

def ternaryVector (r : ℕ) (i : Fin r) : Fin r → ZMod 3 :=
  fun j => if j = i then 1 else 0

def projectiveDirection {V : Type*} [AddGroup V] (x : V) : Set V :=
  {x, -x}

def ternarySpecialVector (r : ℕ) (h : 3 ≤ r) : Fin r → ZMod 3 :=
  ∑ i : Fin 3, ternaryVector r (Fin.castLE h i)

def ternaryCapDirections (r : ℕ) (h : 3 ≤ r) : Set (Set (Fin r → ZMod 3)) :=
  Set.range (fun i : Fin r => projectiveDirection (ternaryVector r i)) ∪
    {projectiveDirection (ternarySpecialVector r h)}

def ternarySelectedVectors (r : ℕ) (h : 3 ≤ r) : Set (Fin r → ZMod 3) :=
  {v | ∃ D, D ∈ ternaryCapDirections r h ∧ v ∈ D}

def ternarySpans (r : ℕ) (h : 3 ≤ r) : Prop :=
  Submodule.span (ZMod 3) (ternarySelectedVectors r h) = ⊤

def ternaryProjectiveCap (r : ℕ) (h : 3 ≤ r) : Prop :=
  ∀ D₁ D₂ D₃ : Set (Fin r → ZMod 3),
    D₁ ∈ ternaryCapDirections r h →
    D₂ ∈ ternaryCapDirections r h →
    D₃ ∈ ternaryCapDirections r h →
    D₁ ≠ D₂ → D₁ ≠ D₃ → D₂ ≠ D₃ →
    ∀ a, a ∈ D₁ → ∀ b, b ∈ D₂ → ∀ c, c ∈ D₃ →
      c ∉ Submodule.span (ZMod 3) ({a, b} : Set (Fin r → ZMod 3))

/-- R-4676, S1: the displayed directions span and form a projective cap for
all r at least three, in particular for r=6 and r=7. -/
def claim52942 : Prop :=
  ∀ (r : ℕ) (h : 3 ≤ r),
    ternarySpans r h ∧ ternaryProjectiveCap r h

/-- The Cayley adjacency relation for a connection set in the ternary vector
space. -/
def ternaryCayleyAdjacency (r : ℕ) (S : Set (Fin r → ZMod 3))
    (x y : Fin r → ZMod 3) : Prop :=
  y - x ∈ S

def ternaryConnectionSet (r : ℕ) (h : 3 ≤ r) : Set (Fin r → ZMod 3) :=
  ternarySelectedVectors r h

/-- R-4676, S2: the selected directions give the inverse-closed Cayley graph
with the stated induced four-cycle and its two absent chords. -/
def claim52943 : Prop :=
  ∀ (r : ℕ) (h : 3 ≤ r),
    let e₁ := ternaryVector r (Fin.castLE h (0 : Fin 3))
    let e₂ := ternaryVector r (Fin.castLE h (1 : Fin 3))
    let e₃ := ternaryVector r (Fin.castLE h (2 : Fin 3))
    let w := ternarySpecialVector r h
    let S := ternaryConnectionSet r h
    S = {x | -x ∈ S} ∧
      ternaryCayleyAdjacency r S 0 e₁ ∧
      ternaryCayleyAdjacency r S e₁ (e₁ + e₂) ∧
      ternaryCayleyAdjacency r S (e₁ + e₂) w ∧
      ternaryCayleyAdjacency r S w 0 ∧
      ¬ ternaryCayleyAdjacency r S 0 (e₁ + e₂) ∧
      ¬ ternaryCayleyAdjacency r S e₁ w ∧
      projectiveDirection (e₁ + e₂) ∉ ternaryCapDirections r h ∧
      projectiveDirection (e₂ + e₃) ∉ ternaryCapDirections r h

end TernaryCap

end MathlibPlus.Open.ResearchFormalization
