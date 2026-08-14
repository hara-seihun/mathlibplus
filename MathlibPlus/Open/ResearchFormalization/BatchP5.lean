import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchP5

abbrev P5 := ZMod 5
abbrev P5Space := Fin 3 → P5

def row3 (a b c : P5) (j : Fin 3) : P5 :=
  if j.val = 0 then a else if j.val = 1 then b else c

def M1 : Matrix (Fin 3) (Fin 3) P5 :=
  fun i => if i.val = 0 then row3 2 2 2
    else if i.val = 1 then row3 0 2 0 else row3 0 2 3

def M2 : Matrix (Fin 3) (Fin 3) P5 :=
  fun i => if i.val = 0 then row3 4 2 2
    else if i.val = 1 then row3 1 1 4 else row3 1 0 1

def M3 : Matrix (Fin 3) (Fin 3) P5 :=
  fun i => if i.val = 0 then row3 0 2 1
    else if i.val = 1 then row3 2 0 3 else row3 2 1 4

def p5LinearMatrix : Matrix (Fin 3) (Fin 3) P5 := M3 * M2 * M1

def p5MatrixAction (M : Matrix (Fin 3) (Fin 3) P5) : P5Space → P5Space :=
  fun x => M.mulVec x

def p5U (x : P5Space) : P5Space :=
  fun i => if i.val = 0 then x 0
    else if i.val = 1 then x 1 else x 2 + 2 * x 0 * (x 1) ^ 2

def p5V (x : P5Space) : P5Space :=
  fun i => if i.val = 0 then x 0
    else if i.val = 1 then x 1 + 3 * x 0 * (x 2) ^ 2 else x 2

def p5q₀ : P5Space → P5Space :=
  p5V ∘ p5U ∘ p5MatrixAction p5LinearMatrix

noncomputable def p5q₀Inv : P5Space → P5Space :=
  Function.invFun p5q₀

noncomputable def p5Tau (v s : P5Space) : P5Space :=
  p5q₀Inv (p5q₀ (v + s) - p5q₀ v)

def p5Generator (s t : P5Space) : Prop :=
  ∃ v : P5Space, t = p5Tau v s ∨ t = -p5Tau v s

noncomputable def p5Class (s : P5Space) : Set P5Space :=
  {t | Relation.EqvGen p5Generator s t}

def p5Ell (s : P5Space) : P5 :=
  6 * s 0 + 28 * s 1 + 33 * s 2

def p5BlockZero : Set P5Space := {0}
def p5BlockKernel : Set P5Space := {s | s ≠ 0 ∧ p5Ell s = 0}
def p5BlockSquareOne : Set P5Space := {s | p5Ell s ^ 2 = 1}
def p5BlockSquareFour : Set P5Space := {s | p5Ell s ^ 2 = 4}

noncomputable def p5BlockCard (B : Set P5Space) : ℕ := by
  classical
  letI := Fintype.ofFinite {s : P5Space // s ∈ B}
  exact Fintype.card {s : P5Space // s ∈ B}

/-- The fully specified p=5 transport partition and its four exact blocks. -/
def p5NonlinearTransportPartition : Prop :=
  Function.Bijective p5q₀ ∧
  (∀ v, p5q₀Inv (p5q₀ v) = v) ∧
  (∀ s, s = 0 → p5Class s = p5BlockZero) ∧
  (∀ s, s ≠ 0 → p5Ell s = 0 → p5Class s = p5BlockKernel) ∧
  (∀ s, p5Ell s ^ 2 = 1 → p5Class s = p5BlockSquareOne) ∧
  (∀ s, p5Ell s ^ 2 = 4 → p5Class s = p5BlockSquareFour) ∧
  (∀ s, s = 0 ∨ (s ≠ 0 ∧ p5Ell s = 0) ∨
    p5Ell s ^ 2 = 1 ∨ p5Ell s ^ 2 = 4) ∧
  p5BlockCard p5BlockZero = 1 ∧
  p5BlockCard p5BlockKernel = 24 ∧
  p5BlockCard p5BlockSquareOne = 50 ∧
  p5BlockCard p5BlockSquareFour = 50

def p5BlockAt (j : Fin 4) : Set P5Space :=
  if j.val = 0 then p5BlockZero
  else if j.val = 1 then p5BlockKernel
  else if j.val = 2 then p5BlockSquareOne
  else p5BlockSquareFour

def p5BlockUnion (J : Set (Fin 4)) : Set P5Space :=
  ⋃ j ∈ J, p5BlockAt j

def paddedSlice {W : Type*} (S : Set (P5Space × W)) (w : W) : Set P5Space :=
  {v | (v, w) ∈ S}

def paddedQ {W : Type*} (z : P5Space × W) : P5Space × W :=
  (p5q₀ z.1, z.2)

def paddedL {W : Type*} (z : P5Space × W) : P5Space × W :=
  (p5MatrixAction p5LinearMatrix z.1, z.2)

/-- Every padded slice saturated by the four p=5 blocks has the same image
under the nonlinear map and its displayed linear shadow. -/
def p5PaddedSliceLinearShadow : Prop :=
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  ∀ (W : Type*) [AddCommGroup W] [Module P5 W]
    [FiniteDimensional P5 W] (S : Set (P5Space × W)),
    (∀ w : W, ∃ J : Set (Fin 4), paddedSlice S w = p5BlockUnion J) →
      paddedQ '' S = paddedL '' S

end MathlibPlus.Open.ResearchFormalization.BatchP5
