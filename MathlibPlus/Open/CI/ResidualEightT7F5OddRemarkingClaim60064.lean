import Mathlib

namespace MathlibPlus.Open.CI_EK8SquarefreeResidual

abbrev F5 := ZMod 5
abbrev M3 := Matrix (Fin 3) (Fin 3) F5

def S : M3 := !![
  3, 1, 0;
  3, 0, 1;
  1, 0, 0
]

def T : M3 := !![
  1, 1, 1;
  2, 0, 4;
  2, 0, 2
]

def A : M3 := !![
  1, 2, 4;
  0, 0, 0;
  2, 4, 3
]

def B3 : M3 := !![
  2, 4, 4;
  4, 1, 3;
  0, 1, 0
]

def C3 : M3 := !![
  2, 2, 4;
  3, 4, 1;
  3, 0, 1
]

def B7 : M3 := !![
  3, 4, 1;
  1, 1, 2;
  0, 1, 0
]

def C7 : M3 := !![
  2, 3, 4;
  3, 1, 1;
  3, 0, 1
]

def L15 : Submodule F5 M3 := Submodule.span F5 ({A} : Set M3)
def W3 : Submodule F5 M3 := Submodule.span F5 ({B3, C3} : Set M3)
def W7 : Submodule F5 M3 := Submodule.span F5 ({B7, C7} : Set M3)

def channelProduct (U V : Submodule F5 M3) : Set M3 :=
  Set.image2 (fun X Y : M3 => X * Y) (U : Set M3) (V : Set M3)

def noNonzeroAlternatingComposition (U V : Submodule F5 M3) : Prop :=
  ∀ x y : M3, x ∈ U → y ∈ V → x * y = 0 ∧ y * x = 0

def claim60064 : Prop :=
  (A * S = T * A ∧ T * A = T ^ 5 * A) ∧
  B3 * S = T ^ 3 * B3 ∧
  C3 * S = T ^ 3 * C3 ∧
  B7 * S = T ^ 7 * B7 ∧
  C7 * S = T ^ 7 * C7 ∧
  A ^ 2 = (4 : F5) • A ∧
  Module.finrank F5 L15 = 1 ∧
  Module.finrank F5 W3 = 2 ∧
  Module.finrank F5 W7 = 2 ∧
  channelProduct L15 W3 = ({0} : Set M3) ∧
  channelProduct W3 L15 = ({0} : Set M3) ∧
  channelProduct L15 W7 = ({0} : Set M3) ∧
  channelProduct W7 L15 = ({0} : Set M3) ∧
  noNonzeroAlternatingComposition L15 W3 ∧
  noNonzeroAlternatingComposition L15 W7

end MathlibPlus.Open.CI_EK8SquarefreeResidual
