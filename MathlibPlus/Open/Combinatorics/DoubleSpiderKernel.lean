import Mathlib

namespace MathlibPlus.Open.Combinatorics

noncomputable section
open Classical

/-- A bounded four-arm tuple; the positivity and sum conditions below select cards. -/
structure ArmCard (A : ℕ) where
  first : Fin (A + 1)
  second : Fin (A + 1)
  third : Fin (A + 1)
  fourth : Fin (A + 1)
  deriving DecidableEq, Fintype

def armSum {A : ℕ} (v : ArmCard A) : ℕ :=
  v.first.val + v.second.val + v.third.val + v.fourth.val

def isPositiveArm (A : ℕ) (v : ArmCard A) : Prop :=
  0 < v.first.val ∧ 0 < v.second.val ∧ 0 < v.third.val ∧
    0 < v.fourth.val ∧ armSum v = A

/-- The three switches are the two within-end swaps and the end swap in W. -/
def wTransform {A : ℕ} (swap₁ swap₂ exchange : Bool) (v : ArmCard A) : ArmCard A :=
  let a := if swap₁ then v.second else v.first
  let b := if swap₁ then v.first else v.second
  let c := if swap₂ then v.fourth else v.third
  let d := if swap₂ then v.third else v.fourth
  if exchange then ⟨c, d, a, b⟩ else ⟨a, b, c, d⟩

abbrev W := Bool × Bool × Bool

/-- The W-orbit represented as a finite set of its eight transforms. -/
def wOrbit {A : ℕ} (v : ArmCard A) : Finset (ArmCard A) :=
  { wTransform false false false v
  , wTransform true false false v
  , wTransform false true false v
  , wTransform true true false v
  , wTransform false false true v
  , wTransform true false true v
  , wTransform false true true v
  , wTransform true true true v }

abbrev TargetCoordinate (A : ℕ) := Finset (ArmCard A)

/-- The target-column predicate: precisely the W-orbits of positive compositions. -/
def isTargetOrbit (A : ℕ) (T : TargetCoordinate A) : Prop :=
  ∃ v, isPositiveArm A v ∧ T = wOrbit v

/-- The target coordinate associated with one positive arm tuple. -/
def targetOf {A : ℕ} (v : ArmCard A) : TargetCoordinate A := wOrbit v

/-- The target automorphism order is the W-stabilizer order. -/
noncomputable def targetAutomorphismOrder {A : ℕ} (T : TargetCoordinate A) : ℕ :=
  if h : isTargetOrbit A T then
    let v : ArmCard A := Classical.choose h
    (Finset.univ.filter fun w : W =>
      wTransform w.1 w.2.1 w.2.2 v = v).card
  else 0

/-- The four-way arm coordinate used by the unit-facet condition. -/
def armCoord {A : ℕ} (i : Fin 4) (v : ArmCard A) : ℕ :=
  if i = 0 then v.first.val
  else if i = 1 then v.second.val
  else if i = 2 then v.third.val
  else v.fourth.val

/-- Add one to the arm selected by a four-way index.  On the admitted positive
sum-(A-1) tuples this is the stated beta + e_i operation. -/
def armUp {A : ℕ} (i : Fin 4) (v : ArmCard (A - 1)) : ArmCard A :=
  ⟨Fin.ofNat (A + 1) (if i = 0 then v.first.val + 1 else v.first.val)
  , Fin.ofNat (A + 1) (if i = 1 then v.second.val + 1 else v.second.val)
  , Fin.ofNat (A + 1) (if i = 2 then v.third.val + 1 else v.third.val)
  , Fin.ofNat (A + 1) (if i = 3 then v.fourth.val + 1 else v.fourth.val)⟩

def zeroArm (A : ℕ) : ArmCard A :=
  ⟨Fin.ofNat (A + 1) 0, Fin.ofNat (A + 1) 0,
    Fin.ofNat (A + 1) 0, Fin.ofNat (A + 1) 0⟩

/-- Bulk and unit-facet rows are indexed by a row kind and a W-orbit at sum
A-1.  `false` is the bulk row and `true` is the unit-facet row. -/
abbrev CurvatureRow (A : ℕ) := Bool × TargetCoordinate (A - 1)

noncomputable def rowRepresentative {A : ℕ} (r : CurvatureRow A) : ArmCard (A - 1) :=
  if h : isTargetOrbit (A - 1) r.2 then Classical.choose h else zeroArm (A - 1)

/-- The grafting-gauge rows U_beta and F_beta from the admitted repair context. -/
noncomputable def rowEntryGraft (K : Type*) [Field K] {A : ℕ}
    (r : CurvatureRow A) (T : TargetCoordinate A) : K :=
  if isTargetOrbit (A - 1) r.2 ∧ isTargetOrbit A T then
    let β := rowRepresentative r
    Finset.univ.sum fun i =>
      if r.1 = true then
        if armCoord i β = 1 then
          if T = wOrbit (armUp i β) then (1 : K) else 0
        else 0
      else if T = wOrbit (armUp i β) then (1 : K) else 0
  else 0

/-- The deletion-gauge matrix entries, with the admitted automorphism-order
factor relating them to grafting gauge. -/
noncomputable def rowEntryDelete (K : Type*) [Field K] {A : ℕ}
    (r : CurvatureRow A) (T : TargetCoordinate A) : K :=
  ((targetAutomorphismOrder T : K) /
      (targetAutomorphismOrder r.2 : K)) * rowEntryGraft K r T

def kernelIndex (m : ℕ) := {j : ℕ // j ∈ Finset.Icc 2 (m - 1)}

/-- The first displayed family of target tuples. -/
def firstKernelTuple (m j : ℕ) : ArmCard (2 * m) :=
  ⟨Fin.ofNat (2 * m + 1) 1, Fin.ofNat (2 * m + 1) 1,
    Fin.ofNat (2 * m + 1) j,
    Fin.ofNat (2 * m + 1) (2 * m - 2 - j)⟩

/-- The second displayed family of target tuples. -/
def secondKernelTuple (m j : ℕ) : ArmCard (2 * m) :=
  ⟨Fin.ofNat (2 * m + 1) 1, Fin.ofNat (2 * m + 1) j,
    Fin.ofNat (2 * m + 1) 1,
    Fin.ofNat (2 * m + 1) (2 * m - 2 - j)⟩

/-- The coefficients in grafting gauge, supported on the two displayed families. -/
noncomputable def omegaGraft (K : Type*) [Field K] (m : ℕ) :
    TargetCoordinate (2 * m) → K := fun T =>
  ((Finset.Icc 2 (m - 1)).attach.sum fun j =>
    if T = targetOf (firstKernelTuple m j.1) then
      (-2 : K) * (-1 : K) ^ j.1
    else 0) +
  ((Finset.Icc 2 (m - 1)).attach.sum fun j =>
    if T = targetOf (secondKernelTuple m j.1) then
      (1 : K) * (-1 : K) ^ j.1
    else 0)

/-- Divide the displayed coefficients by the target automorphism order in
 deletion gauge. -/
noncomputable def omegaDelete (K : Type*) [Field K] (m : ℕ) :
    TargetCoordinate (2 * m) → K := fun T =>
  omegaGraft K m T / (targetAutomorphismOrder T : K)

/-- Kernel membership for the explicit deletion-gauge matrix, restricted to the
admitted target-orbit coordinates. -/
def isKernelVector (K : Type*) [Field K] {A : ℕ}
    (x : TargetCoordinate A → K) : Prop :=
  (∀ T, ¬ isTargetOrbit A T → x T = 0) ∧
  (∀ r : CurvatureRow A,
    ∑ T : TargetCoordinate A, rowEntryDelete K r T * x T = 0)

/-- Explicit even-A kernel vector: its kernel is one-dimensional, its only
coordinates are the two displayed families with the displayed coefficients,
and deletion gauge divides by the target automorphism order. -/
def explicitEvenKernelVector : Prop :=
  ∀ (K : Type*) [Field K] [CharZero K] (m : ℕ),
    let ω := omegaDelete K m
    (isKernelVector K ω)
    ∧ (∀ x : TargetCoordinate (2 * m) → K,
        isKernelVector K x → ∃ c : K, ∀ T, x T = c * ω T)
    ∧ (∃ T, ω T ≠ 0)
    ∧ (∀ j : kernelIndex m,
        ω (targetOf (firstKernelTuple m j.1)) =
          ((-2 : K) * (-1 : K) ^ j.1) /
            (targetAutomorphismOrder
              (targetOf (firstKernelTuple m j.1)) : K))
    ∧ (∀ j : kernelIndex m,
        ω (targetOf (secondKernelTuple m j.1)) =
          ((1 : K) * (-1 : K) ^ j.1) /
            (targetAutomorphismOrder
              (targetOf (secondKernelTuple m j.1)) : K))
    ∧ (∀ T : TargetCoordinate (2 * m),
        (∀ j : kernelIndex m,
          T ≠ targetOf (firstKernelTuple m j.1) ∧
          T ≠ targetOf (secondKernelTuple m j.1)) →
        ω T = 0)

end
end MathlibPlus.Open.Combinatorics
