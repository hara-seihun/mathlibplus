import Mathlib

namespace MathlibPlus.Open.Research

namespace SupportFourBatch

abbrev BaseScalar := ZMod 2
abbrev A := Fin 3 → BaseScalar
abbrev FiberScalar := ZMod 3
abbrev B := Fin 2 → FiberScalar
abbrev Point := A × B

-- The binary labels 0 through 7 in the fixed coordinate order of C₂³.
def a0 : A := ![0, 0, 0]
def a1 : A := ![1, 0, 0]
def a2 : A := ![0, 1, 0]
def a3 : A := ![1, 1, 0]
def a4 : A := ![0, 0, 1]
def a5 : A := ![1, 0, 1]
def a6 : A := ![0, 1, 1]
def a7 : A := ![1, 1, 1]

def basePermutation : Equiv.Perm A := Equiv.swap a6 a7
def activeSupport : Set A := {a1, a2, a3, a4}

def displacement (q : Equiv.Perm B) : Set B :=
  Set.range (fun b => q b - b)

def fiberLine (L : Submodule FiberScalar B) : Prop :=
  L ≠ ⊥ ∧ Module.finrank FiberScalar L = 1

/-- Claim 37562: the support-four one-translation/two-lines/full-row profile. -/
def claim37562 (f : Equiv.Perm Point) : Prop :=
  ∃ q : A → Equiv.Perm B,
    (∀ a b, f (a, b) = (basePermutation a, q a b)) ∧
    (∀ a, a ∉ activeSupport → q a = 1) ∧
    (∃ t : B, t ≠ 0 ∧ ∀ b, q a1 b = b + t) ∧
    (∃ L₀ L₁ : Submodule FiberScalar B,
      fiberLine L₀ ∧
      fiberLine L₁ ∧
      L₀ ≠ L₁ ∧
      displacement (q a2) = (L₀ : Set B) ∧
      displacement (q a3) = (L₁ : Set B)) ∧
    displacement (q a4) = Set.univ

end SupportFourBatch

end MathlibPlus.Open.Research
