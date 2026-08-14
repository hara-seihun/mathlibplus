import Mathlib

namespace MathlibPlus.Open.Research.R2211

abbrev F3 := ZMod 3
abbrev H := F3 × F3 × F3 × F3 × F3
abbrev FunctionSpace := H → F3

def coordI (h : H) : F3 := h.1
def coordJ (h : H) : F3 := h.2.1
def coordA (h : H) : F3 := h.2.2.1
def coordB (h : H) : F3 := h.2.2.2.1
def coordC (h : H) : F3 := h.2.2.2.2

def nonlinearBasis : Fin 6 → FunctionSpace
  | 0 => fun _ => 1
  | 1 => coordI
  | 2 => coordA
  | 3 => fun h => coordI h ^ 2
  | 4 => fun h => coordI h * coordA h
  | 5 => fun h => coordA h ^ 2

def K_NL : Submodule F3 FunctionSpace :=
  Submodule.span F3 (Set.range nonlinearBasis)

def gMap : H → H := fun h =>
  let i := coordI h
  let j := coordJ h
  let a := coordA h
  let b := coordB h
  let c := coordC h
  (i, j, a + i * (i - 1), b + (2 * i - 1) * j, c + j ^ 2)

def aSquare : FunctionSpace := fun h => coordA h ^ 2

def gPullback (f : FunctionSpace) : FunctionSpace := f ∘ gMap

def gPullbackModule : Submodule F3 FunctionSpace :=
  Submodule.span F3
    {f | ∃ u : FunctionSpace, u ∈ K_NL ∧ f = gPullback u}

def explicitGPullbackASquare : FunctionSpace := fun h =>
  (coordA h + coordI h * (coordI h - 1)) ^ 2

def QuadraticMapLeavesModule : Prop :=
  gPullback aSquare = explicitGPullbackASquare ∧
    gPullback aSquare ∉ K_NL ∧
    Module.finrank F3 ↥(K_NL ⊔ gPullbackModule) = 7

end MathlibPlus.Open.Research.R2211
