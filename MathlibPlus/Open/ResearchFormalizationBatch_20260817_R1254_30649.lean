import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254

noncomputable section

abbrev RepairF3_30649 := ZMod 3
abbrev RepairBase30649 (a : ℕ) := Fin a → RepairF3_30649
abbrev RepairFiber30649 (m : ℕ) := Fin m → RepairF3_30649

/-- The fibre shear `q_f(x,v)=(x,v+f(x))`. -/
def repairFiberShear30649 {a m : ℕ}
    (f : RepairBase30649 a → RepairFiber30649 m) :
    RepairBase30649 a × RepairFiber30649 m →
      RepairBase30649 a × RepairFiber30649 m :=
  fun xv => (xv.1, xv.2 + f xv.1)

/-- The affine map determined by the values at the origin and the coordinate
points. -/
def repairAffinePart30649 {a m : ℕ}
    (f : RepairBase30649 a → RepairFiber30649 m)
    (x : RepairBase30649 a) : RepairFiber30649 m :=
  f 0 + ∑ i : Fin a,
    (x i) • (f (Pi.single i 1) - f 0)

/-- A canonical representative modulo affine fibre maps. -/
def repairAffineNormalized30649 {a m : ℕ}
    (f : RepairBase30649 a → RepairFiber30649 m)
    (x : RepairBase30649 a) : RepairFiber30649 m :=
  f x - repairAffinePart30649 f x

/-- The translated second difference in the direction `x`. -/
def repairSecondDifference30649 {a m : ℕ}
    (f : RepairBase30649 a → RepairFiber30649 m)
    (x b c : RepairBase30649 a) : RepairFiber30649 m :=
  (f (x + c + b) - f (x + c)) - (f (c + b) - f c)

/-- The paired vertical motion space `F_x=E_x+E_{-x}`. -/
def repairPairedMotion30649 {a m : ℕ}
    (f : RepairBase30649 a → RepairFiber30649 m)
    (x : RepairBase30649 a) : Submodule RepairF3_30649 (RepairFiber30649 m) :=
  Submodule.span RepairF3_30649
    {v | ∃ b c : RepairBase30649 a,
      v = repairSecondDifference30649 f x b c ∨
        v = repairSecondDifference30649 f (-x) b c}

/-- Existence of the linear correction after the affine normalization that is
intrinsic to the fibre-shear conjugacy problem. -/
def repairLinearCorrection30649 {a m : ℕ}
    (f : RepairBase30649 a → RepairFiber30649 m) : Prop :=
  ∃ ell : RepairBase30649 a →ₗ[RepairF3_30649] RepairFiber30649 m,
    ∀ x : RepairBase30649 a,
      repairAffineNormalized30649 f x + ell x ∈ repairPairedMotion30649 f x

/-- Claim 30649: for arbitrary (not necessarily odd) fibre maps, the linear
correction exists on every ternary square and on ternary cubes of fibre rank
at most four. -/
def claim30649 : Prop :=
  ∀ (a m : ℕ) (f : RepairBase30649 a → RepairFiber30649 m),
    (a = 2 ∨ (a = 3 ∧ m ≤ 4)) →
      repairLinearCorrection30649 f

end
end MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254
