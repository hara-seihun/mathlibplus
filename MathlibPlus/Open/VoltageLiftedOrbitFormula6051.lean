import Mathlib

namespace MathlibPlus.Open

namespace LiftedOrbit

/-- A signed generator letter, where `true` denotes a generator and `false` its inverse. -/
abbrev Letter (I : Type*) := I × Bool

def baseStep {B I : Type*} (r : I → Equiv.Perm B)
    (l : Letter I) (b : B) : B :=
  if l.2 then r l.1 b else (r l.1).symm b

def liftStep {p : ℕ} {B I : Type*} (r : I → Equiv.Perm B)
    (β : I → B → ZMod p) (l : Letter I) (x : ZMod p × B) : ZMod p × B :=
  if l.2 then (x.1 + β l.1 x.2, r l.1 x.2)
  else (x.1 - β l.1 ((r l.1).symm x.2), (r l.1).symm x.2)

def baseWord {B I : Type*} (r : I → Equiv.Perm B) :
    List (Letter I) → B → B
  | [], b => b
  | l :: w, b => baseWord r w (baseStep r l b)

def liftWord {p : ℕ} {B I : Type*} (r : I → Equiv.Perm B)
    (β : I → B → ZMod p) :
    List (Letter I) → ZMod p × B → ZMod p × B
  | [], x => x
  | l :: w, x => liftWord r β w (liftStep r β l x)

def baseOrbit {B I : Type*} (r : I → Equiv.Perm B) (b₀ : B) : Set B :=
  {b | ∃ w : List (Letter I), baseWord r w b₀ = b}

def closedVoltages {p : ℕ} {B I : Type*} (r : I → Equiv.Perm B)
    (β : I → B → ZMod p) (b₀ : B) : Set (ZMod p) :=
  {v | ∃ w : List (Letter I),
    baseWord r w b₀ = b₀ ∧ (liftWord r β w (0, b₀)).1 = v}

def closedVoltageSubgroup {p : ℕ} {B I : Type*} (r : I → Equiv.Perm B)
    (β : I → B → ZMod p) (b₀ : B) : AddSubgroup (ZMod p) :=
  AddSubgroup.closure (closedVoltages r β b₀)

structure SpanningTreePaths {B I : Type*}
    (r : I → Equiv.Perm B) (b₀ : B) where
  path : B → List (Letter I)
  endpoint : ∀ b, b ∈ baseOrbit r b₀ → baseWord r (path b) b₀ = b
  root : path b₀ = []

def treePotential {p : ℕ} {B I : Type*} (r : I → Equiv.Perm B)
    (β : I → B → ZMod p) (b₀ : B) (paths : SpanningTreePaths r b₀) (b : B) : ZMod p :=
  (liftWord r β (paths.path b) (0, b₀)).1

def liftedOrbit {p : ℕ} {B I : Type*} (r : I → Equiv.Perm B)
    (β : I → B → ZMod p) (b₀ : B) (z : ZMod p) : Set (ZMod p × B) :=
  {x | ∃ w : List (Letter I), liftWord r β w (z, b₀) = x}

def cosetOrbit {p : ℕ} {B I : Type*} (r : I → Equiv.Perm B)
    (β : I → B → ZMod p) (b₀ : B) (paths : SpanningTreePaths r b₀)
    (W : AddSubgroup (ZMod p)) (a : (ZMod p) ⧸ W) : Set (ZMod p × B) :=
  {x | ∃ z : ZMod p, QuotientAddGroup.mk z = a ∧
    ∃ b : B, b ∈ baseOrbit r b₀ ∧
      ∃ w : W, x = (z + treePotential r β b₀ paths b + (w : ZMod p), b)}

/--
The exact lifted-orbit description for a finite base and a prime voltage fibre.
The representative `z` in `cosetOrbit` realizes the informal index
`a ∈ 𝔽_p / W_O`.
-/
def liftedOrbitFormula
    {p : ℕ} [Fact p.Prime]
    {B : Type*} [Fintype B]
    {I : Type*}
    (r : I → Equiv.Perm B)
    (β : I → B → ZMod p)
    (b₀ : B)
    (paths : SpanningTreePaths r b₀) : Prop :=
  let W := closedVoltageSubgroup r β b₀
  (∀ a : (ZMod p) ⧸ W, ∀ z : ZMod p,
      QuotientAddGroup.mk z = a →
        liftedOrbit r β b₀ z = cosetOrbit r β b₀ paths W a) ∧
    (∀ a₁ a₂ : (ZMod p) ⧸ W,
      cosetOrbit r β b₀ paths W a₁ = cosetOrbit r β b₀ paths W a₂ ↔ a₁ = a₂)

end LiftedOrbit

end MathlibPlus.Open
