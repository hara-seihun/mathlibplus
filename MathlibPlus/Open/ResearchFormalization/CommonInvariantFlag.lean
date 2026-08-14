import Mathlib

namespace MathlibPlus.Open.CommonInvariantFlag

abbrev F := ZMod 5
abbrev V := Fin 3 → F

def S (v : V) : V :=
  ![3 * v 0 + v 1, 3 * v 0 + v 2, v 0]

def T (v : V) : V :=
  ![v 0 + v 1 + v 2, 2 * v 0 + 4 * v 2, 2 * v 0 + 2 * v 2]

def Sdual (w : V) : V :=
  ![3 * w 0 + 3 * w 1 + w 2, w 0, w 1]

def Tdual (w : V) : V :=
  ![w 0 + 2 * w 1 + 2 * w 2, w 0, w 0 + 4 * w 1 + 2 * w 2]

def vLine : V := ![(1 : F), 0, 2]
def wLine : V := ![(1 : F), 2, 4]
def hBasis₁ : V := ![(3 : F), 1, 0]
def hBasis₂ : V := ![(1 : F), 0, 1]

def L : Submodule F V := Submodule.span F {vLine}
def H : Submodule F V := Submodule.span F {hBasis₁, hBasis₂}

def commonInvariant (W : Submodule F V) : Prop :=
  ∀ v, v ∈ W → S v ∈ W ∧ T v ∈ W

def commonEigenPrimal (v : V) : Prop :=
  v ≠ 0 ∧ (∃ a : F, S v = a • v) ∧ (∃ b : F, T v = b • v)

def commonEigenDual (w : V) : Prop :=
  w ≠ 0 ∧ (∃ a : F, Sdual w = a • w) ∧ (∃ b : F, Tdual w = b • w)

def claim59548 : Prop :=
  (∀ v : V,
    commonEigenPrimal v ↔
      ∃ c : F, c ≠ 0 ∧ v = c • vLine ∧
        S v = 3 • v ∧ T v = 3 • v) ∧
  (∀ w : V,
    commonEigenDual w ↔
      ∃ c : F, c ≠ 0 ∧ w = c • wLine ∧
        Sdual w = 3 • w ∧ Tdual w = 3 • w) ∧
  (∀ v : V, v ∈ H ↔ v 0 + 2 * v 1 + 4 * v 2 = 0) ∧
  IsCompl L H ∧
  commonInvariant L ∧ commonInvariant H ∧
  (∀ W : Submodule F V, commonInvariant W →
    W = ⊥ ∨ W = L ∨ W = H ∨ W = ⊤) ∧
  (∀ W : Submodule F V, commonInvariant W → W ≤ H →
    W = ⊥ ∨ W = H)

end MathlibPlus.Open.CommonInvariantFlag
