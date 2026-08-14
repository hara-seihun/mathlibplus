import Mathlib

open scoped BigOperators Classical
noncomputable section

namespace MathlibPlus.Open.ProjectsResearch

structure OrbitType45143 where
  i : Fin 4
  j : Fin 11
  k : Fin 11
  z : Bool
  deriving DecidableEq, Fintype

def retained45143 (t : OrbitType45143) : Prop :=
  t.i.val = 3 ∨ t.j.val = 10 ∨ t.k.val = 10

def retainedTypes45143 : Finset OrbitType45143 :=
  Finset.univ.filter retained45143

def typeM145143 : OrbitType45143 := ⟨3, 0, 0, false⟩
def typeM245143 : OrbitType45143 := ⟨0, 10, 0, false⟩
def typeM345143 : OrbitType45143 := ⟨0, 0, 10, false⟩

def orbitWeight45143 (t : OrbitType45143) : ℕ :=
  Nat.choose 3 t.i.val * Nat.choose 10 t.j.val * Nat.choose 10 t.k.val

def possibleUnionCard45143 (cap a b c : ℕ) : Prop :=
  max a b ≤ c ∧ c ≤ min cap (a + b)

def allowedUnion45143 (a b c : OrbitType45143) : Prop :=
  possibleUnionCard45143 3 a.i.val b.i.val c.i.val ∧
    possibleUnionCard45143 10 a.j.val b.j.val c.j.val ∧
    possibleUnionCard45143 10 a.k.val b.k.val c.k.val ∧
    ((a.z || b.z) = c.z)

def orbitMass45143 (x : OrbitType45143 → ℚ) : ℚ :=
  ∑ t ∈ retainedTypes45143, (orbitWeight45143 t : ℚ) * x t

def chooseContaining45143 (cap n : ℕ) : ℕ :=
  if 0 < n then Nat.choose (cap - 1) (n - 1) else 0

def orbitFreqM145143 (x : OrbitType45143 → ℚ) : ℚ :=
  ∑ t ∈ retainedTypes45143,
    (chooseContaining45143 3 t.i.val *
      Nat.choose 10 t.j.val * Nat.choose 10 t.k.val : ℚ) * x t

def orbitFreqM245143 (x : OrbitType45143 → ℚ) : ℚ :=
  ∑ t ∈ retainedTypes45143,
    (Nat.choose 3 t.i.val *
      chooseContaining45143 10 t.j.val * Nat.choose 10 t.k.val : ℚ) * x t

def orbitFreqM345143 (x : OrbitType45143 → ℚ) : ℚ :=
  ∑ t ∈ retainedTypes45143,
    (Nat.choose 3 t.i.val * Nat.choose 10 t.j.val *
      chooseContaining45143 10 t.k.val : ℚ) * x t

def orbitFreqZ45143 (x : OrbitType45143 → ℚ) : ℚ :=
  ∑ t ∈ retainedTypes45143, if t.z then
    (orbitWeight45143 t : ℚ) * x t else 0

def orbitHornFeasible45143 (x : OrbitType45143 → ℚ) : Prop :=
  (∀ t ∈ retainedTypes45143, 0 ≤ x t ∧ x t ≤ 1) ∧
    x typeM145143 = 1 ∧ x typeM245143 = 1 ∧ x typeM345143 = 1 ∧
    0 < (∑ t ∈ retainedTypes45143, if t.z then x t else 0) ∧
    (∀ a ∈ retainedTypes45143, ∀ b ∈ retainedTypes45143,
      ∀ c ∈ retainedTypes45143, allowedUnion45143 a b c →
        x a + x b - x c ≤ 1)

/- Claim R-2693.1 (45143), represented by the exact finite predicate of the
specified orbit-quotient Horn relaxation.  This definition is the method
specification itself; it introduces no additional feasibility assertion. -/
/-- Claim R-2693.2 (45144). -/
def claim45144 : Prop :=
  ∃ x : OrbitType45143 → ℚ,
    orbitHornFeasible45143 x ∧
    (retainedTypes45143.filter (fun t => 0 < x t)).card = 36 ∧
    (∀ t ∈ retainedTypes45143, 0 < x t →
      x t = 1 ∨ x t = (1 : ℚ) / 2 ∨ x t = (17 : ℚ) / 38) ∧
    orbitMass45143 x = (5261 : ℚ) / 38 ∧
    orbitFreqM145143 x = (1291 : ℚ) / 19 ∧
    orbitFreqM245143 x = (1291 : ℚ) / 19 ∧
    orbitFreqM345143 x = (1291 : ℚ) / 19 ∧
    orbitMass45143 x - 2 * orbitFreqM145143 x = (97 : ℚ) / 38 ∧
    0 < orbitFreqZ45143 x ∧
    orbitFreqZ45143 x = (1272 : ℚ) / 19

/-- Claim R-2693.3 (45145), in its semantic form: the specified constraints
have a feasible point at which none of the three block coordinates reaches
half of the weighted mass, so no universally valid certificate built only
from those constraints can establish abundance. -/
def claim45145 : Prop :=
  (¬ ∀ x : OrbitType45143 → ℚ,
      orbitHornFeasible45143 x →
        (orbitFreqM145143 x ≥ orbitMass45143 x / 2 ∨
          orbitFreqM245143 x ≥ orbitMass45143 x / 2 ∨
          orbitFreqM345143 x ≥ orbitMass45143 x / 2)) ∧
    ∃ x : OrbitType45143 → ℚ,
      orbitHornFeasible45143 x ∧
        orbitFreqM145143 x < orbitMass45143 x / 2 ∧
        orbitFreqM245143 x < orbitMass45143 x / 2 ∧
        orbitFreqM345143 x < orbitMass45143 x / 2

end MathlibPlus.Open.ProjectsResearch
