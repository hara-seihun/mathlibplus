import Mathlib

namespace MathlibPlus.Open.FiveSevenFrameGlobalSlope

abbrev F5 := ZMod 5
abbrev A := Fin 3 → F5
abbrev B := Fin 4 → F5

abbrev d₁ : B := ![(1 : F5), 0, 0, 0]
abbrev d₂ : B := ![(0 : F5), 1, 0, 0]
abbrev d₃ : B := ![(0 : F5), 0, 1, 0]
abbrev d₄ : B := ![(0 : F5), 0, 0, 1]
abbrev d₅ : B := ![(1 : F5), 1, 1, 1]
abbrev d₆ : B := ![(1 : F5), 2, 3, 4]
abbrev d₇ : B := ![(1 : F5), 4, 4, 1]

def f5Directions : Fin 7 → B := ![d₁, d₂, d₃, d₄, d₅, d₆, d₇]

abbrev u₁ : A := ![(4 : F5), 4, 4]
abbrev u₂ : A := ![(4 : F5), 3, 1]
abbrev u₃ : A := ![(4 : F5), 2, 1]
abbrev u₄ : A := ![(4 : F5), 1, 4]
abbrev u₅ : A := ![(1 : F5), 0, 0]
abbrev u₆ : A := ![(0 : F5), 1, 0]
abbrev u₇ : A := ![(0 : F5), 0, 1]

def f5Covectors : Fin 7 → A := ![u₁, u₂, u₃, u₄, u₅, u₆, u₇]

def f5Pairing (u v : A) : F5 := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def f5SevenFrameEquations (f : B → A) : Prop :=
  ∀ x : B,
    f5Pairing (f5Covectors 0) (f (x + f5Directions 0) - f x) = 1 ∧
      ∀ i : Fin 6,
        f5Pairing (f5Covectors i.succ) (f (x + f5Directions i.succ) - f x) = 0

def f5SevenFrameNoPotential : Prop :=
  ¬∃ f : B → A, f5SevenFrameEquations f

def f5Kernel (i : Fin 7) : Set A :=
  {a | f5Pairing (f5Covectors i) a = 0}

def f5SourceFibres : Set (A × B) :=
  {p | ∃ i : Fin 7, p.1 ∈ f5Kernel i ∧
    (p.2 = f5Directions i ∨ p.2 = -f5Directions i)}

def f5TargetFibres : Set (A × B) :=
  {p |
    (p.2 = f5Directions 0 ∧ f5Pairing (f5Covectors 0) p.1 = 1) ∨
      (p.2 = -f5Directions 0 ∧ f5Pairing (f5Covectors 0) p.1 = -1) ∨
      ∃ i : Fin 6, p.1 ∈ f5Kernel i.succ ∧
        (p.2 = f5Directions i.succ ∨ p.2 = -f5Directions i.succ)}

def f5Shear (f : B → A) : A × B → A × B :=
  fun p => (p.1 + f p.2, p.2)

def f5ShearEdgeDifference (f : B → A) (a : A) (x : B) (h : A) (d : B) : A × B :=
  f5Shear f (a + h, x + d) - f5Shear f (a, x)

def f5ShearCarriesFibredCayleyGraph (f : B → A) : Prop :=
  ∀ (a : A) (x : B) (h : A) (d : B),
    (h, d) ∈ f5SourceFibres ↔
      f5ShearEdgeDifference f a x h d ∈ f5TargetFibres

def f5NoShearCarriesFibredCayleyGraph : Prop :=
  ¬∃ f : B → A, f5ShearCarriesFibredCayleyGraph f

def claim60997 : Prop :=
  f5SevenFrameNoPotential ∧ f5NoShearCarriesFibredCayleyGraph

end MathlibPlus.Open.FiveSevenFrameGlobalSlope
