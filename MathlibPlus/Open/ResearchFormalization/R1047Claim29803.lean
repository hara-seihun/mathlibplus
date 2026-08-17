import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1047Claim29803

noncomputable section

abbrev BooleanSwitchGroup (A B : Type*) := (A × B) × Bool

def booleanSwitch {A B : Type*} [Add A] [Add B]
    (b : A × B → Bool) : BooleanSwitchGroup A B → BooleanSwitchGroup A B :=
  fun g => (g.1, Bool.xor g.2 (b g.1))

def linearityLocus {A B : Type*} [Add A] [Add B]
    (b : A × B → Bool) : Set (A × B) :=
  {x | ∀ u : A × B, b (x + u) = Bool.xor (b x) (b u)}

def derivativeDelta {A B : Type*} [Add A] [Add B]
    (b : A × B → Bool) (x u : A × B) : Bool :=
  Bool.xor (Bool.xor (b (x + u)) (b x)) (b u)

def normalizedDerivative {A B : Type*} [Add A] [Add B]
    (b : A × B → Bool) (u : A × B) :
    BooleanSwitchGroup A B → BooleanSwitchGroup A B :=
  fun g => (g.1, Bool.xor g.2 (derivativeDelta b g.1 u))

def derivativeWord {A B : Type*} [Add A] [Add B]
    (b : A × B → Bool) :
    List (A × B) → BooleanSwitchGroup A B → BooleanSwitchGroup A B
  | [], g => g
  | u :: us, g => derivativeWord b us (normalizedDerivative b u g)

def derivativeOrbit {A B : Type*} [Add A] [Add B]
    (b : A × B → Bool) (g : BooleanSwitchGroup A B) :
    Set (BooleanSwitchGroup A B) :=
  {h | ∃ us : List (A × B), derivativeWord b us g = h}

def singletonFiberPoint {A B : Type*} [Add A] [Add B]
    (x : A × B) (e : Bool) : BooleanSwitchGroup A B :=
  (x, e)

def twoPointFiber {A B : Type*} [Add A] [Add B]
    (x : A × B) : Set (BooleanSwitchGroup A B) :=
  {(x, false), (x, true)}

/-- Claim 29803: with `b(0)=0`, derivative orbits in a linearity-locus
fiber are singleton points, while every nonlinearity-locus fiber is one
whole two-point orbit. -/
def exactBooleanSwitchDerivativeOrbitClassification_claim29803 : Prop :=
  ∀ {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (b : A × B → Bool),
    b (0, 0) = false →
      let Lb := linearityLocus b
      (∀ x : A × B, x ∈ Lb → ∀ e : Bool,
        derivativeOrbit b (singletonFiberPoint x e) =
          ({singletonFiberPoint x e} : Set (BooleanSwitchGroup A B))) ∧
      (∀ x : A × B, x ∉ Lb → ∀ e : Bool,
        derivativeOrbit b (singletonFiberPoint x e) = twoPointFiber x)

end

end MathlibPlus.Open.ResearchFormalization.R1047Claim29803
