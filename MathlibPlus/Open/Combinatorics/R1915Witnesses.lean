import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.Combinatorics.R1915

abbrev BoolCube (n : ℕ) := Fin n → Bool

def xor8 (a b : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (Nat.xor a.1 b.1)

def toggleBool {n : ℕ} (x : BoolCube n) (j : Fin n) : BoolCube n :=
  Function.update x j (Bool.not (x j))

def cubeAddBool {n : ℕ} (x y : BoolCube n) : BoolCube n :=
  fun k => Bool.xor (x k) (y k)

def zeroBool {n : ℕ} : BoolCube n := fun _ => false

def corner8 : Finset (Fin 8) := {0, 1, 2}

def cornerPlane8 : Finset (Fin 8) := {0, 1, 2, 3}

def q7Offsets : Fin 7 → Fin 8 := ![0, 0, 4, 3, 7, 0, 3]

def q7Columns : Fin 7 → Fin 7 → Fin 8 :=
  ![![0, 4, 5, 6, 6, 5, 6],
    ![6, 0, 2, 5, 3, 4, 5],
    ![5, 4, 0, 5, 3, 5, 6],
    ![6, 5, 5, 0, 4, 3, 2],
    ![6, 4, 5, 6, 0, 3, 6],
    ![6, 5, 6, 4, 1, 0, 7],
    ![7, 5, 1, 4, 7, 6, 0]]

def q7AllOffsets : Fin 7 → Fin 8 := fun _ => 3

def q7AllColumns : Fin 7 → Fin 7 → Fin 8 :=
  ![![0, 3, 1, 4, 7, 2, 5],
    ![6, 0, 2, 7, 1, 4, 3],
    ![5, 7, 0, 3, 1, 2, 6],
    ![3, 2, 4, 0, 1, 5, 7],
    ![3, 5, 7, 6, 0, 1, 2],
    ![7, 1, 6, 2, 4, 0, 3],
    ![1, 4, 3, 2, 7, 6, 0]]

def q7Affine (i : Fin 7) (b : Fin 8) (row : Fin 7 → Fin 8)
    (x : BoolCube 7) : Fin 8 :=
  List.foldl xor8 b
    ((Finset.univ.filter (fun k : Fin 7 => k ≠ i ∧ x k = true)).toList.map row)

def q7SeedValue (i : Fin 7) (x : BoolCube 7) : Fin 8 :=
  q7Affine i (q7Offsets i) (q7Columns i) x

def q7AllValue (i : Fin 7) (x : BoolCube 7) : Fin 8 :=
  q7Affine i (q7AllOffsets i) (q7AllColumns i) x

def q7SeedSelected (i : Fin 7) (x : BoolCube 7) : Prop :=
  q7SeedValue i x ∉ corner8

def q7AllSelected (i : Fin 7) (x : BoolCube 7) : Prop :=
  q7AllValue i x ∉ corner8

def q7SeedBool (i : Fin 7) (x : BoolCube 7) : Bool :=
  decide (q7SeedSelected i x)

def q7AllBool (i : Fin 7) (x : BoolCube 7) : Bool :=
  decide (q7AllSelected i x)

def q7Squares : Finset (BoolCube 7 × (Fin 7 × Fin 7)) :=
  (Finset.univ : Finset (BoolCube 7 × (Fin 7 × Fin 7))).filter
    (fun s => s.1 s.2.1 = false ∧ s.1 s.2.2 = false ∧ s.2.1 < s.2.2)

def absentCount7
    (f : Fin 7 → BoolCube 7 → Prop)
    (s : BoolCube 7 × (Fin 7 × Fin 7)) : ℕ :=
  (if f s.2.1 s.1 then 0 else 1) +
    (if f s.2.1 (toggleBool s.1 s.2.2) then 0 else 1) +
    (if f s.2.2 s.1 then 0 else 1) +
    (if f s.2.2 (toggleBool s.1 s.2.1) then 0 else 1)

def q7C4Free (f : Fin 7 → BoolCube 7 → Prop) : Prop :=
  ∀ s ∈ q7Squares, 1 ≤ absentCount7 f s

def q7DirectionalDensity
    (f : Fin 7 → BoolCube 7 → Bool) (i : Fin 7) : ℚ :=
  ((Finset.univ.filter (fun x : BoolCube 7 => x i = false ∧ f i x = true)).card : ℚ) /
    ((Finset.univ.filter (fun x : BoolCube 7 => x i = false)).card : ℚ)

def q7TranslationOrbit
    (f : Fin 7 → BoolCube 7 → Bool) (i : Fin 7) :
    Finset (BoolCube 7 → Bool) :=
  (Finset.univ.filter (fun t : BoolCube 7 => t i = false)).image
    (fun t => fun x => f i (cubeAddBool x t))

def q7EdgeCount (f : Fin 7 → BoolCube 7 → Prop) : ℕ :=
  ∑ i : Fin 7,
    (Finset.univ.filter (fun x : BoolCube 7 => x i = false ∧ f i x)).card

def q7RowSurjective (offset : Fin 7 → Fin 8)
    (columns : Fin 7 → Fin 7 → Fin 8) : Prop :=
  ∀ i : Fin 7, ∀ y : Fin 8,
    ∃ x : BoolCube 7, x i = false ∧ q7Affine i (offset i) (columns i) x = y

def q7SeedCertificate : Prop :=
  q7RowSurjective q7Offsets q7Columns ∧
    (∀ i : Fin 7, (q7TranslationOrbit q7SeedBool i).card = 8) ∧
    (∀ i : Fin 7, q7DirectionalDensity q7SeedBool i = 5 / 8) ∧
    q7Squares.card = 672 ∧
    (Finset.filter (fun s => absentCount7 q7SeedSelected s = 1) q7Squares).card = 372 ∧
    (Finset.filter (fun s => absentCount7 q7SeedSelected s = 2) q7Squares).card = 264 ∧
    (Finset.filter (fun s => absentCount7 q7SeedSelected s = 3) q7Squares).card = 36 ∧
    q7C4Free q7SeedSelected ∧ q7EdgeCount q7SeedSelected = 280

/-- The explicit all-offset missing-corner tournament witness. -/
def allOffsetMissingCornerTournament_34965 : Prop :=
  q7RowSurjective q7AllOffsets q7AllColumns ∧
    (∀ i : Fin 7, q7AllValue i zeroBool = 3) ∧
    q7Squares.card = 672 ∧ q7C4Free q7AllSelected ∧
    (∀ i j : Fin 7, i ≠ j →
      (q7AllColumns i j ∉ cornerPlane8) ↔
        ¬ (q7AllColumns j i ∉ cornerPlane8)) ∧
    (∀ i : Fin 7,
      (Finset.filter
        (fun j : Fin 7 => i ≠ j ∧ q7AllColumns i j ∉ cornerPlane8)
        (Finset.univ : Finset (Fin 7))).card = 3)

def parityExcept {n : ℕ} (j : Fin n) (x : BoolCube n) : Bool :=
  List.foldl Bool.xor false
    ((Finset.univ.filter (fun k : Fin n => k ≠ j)).toList.map x)

def newParityFunction {n : ℕ} (j : Fin n) (x : BoolCube n) : Bool :=
  Bool.not (parityExcept j x)

def newSelected {n : ℕ} (j : Fin n) (x : BoolCube n) : Prop :=
  newParityFunction j x = true

def directionalDensity {n : ℕ}
    (f : Fin n → BoolCube n → Bool) (i : Fin n) : ℚ :=
  ((Finset.univ.filter (fun x : BoolCube n => x i = false ∧ f i x = true)).card : ℚ) /
    ((Finset.univ.filter (fun x : BoolCube n => x i = false)).card : ℚ)

def translationOrbit {n : ℕ}
    (f : Fin n → BoolCube n → Bool) (i : Fin n) :
    Finset (BoolCube n → Bool) :=
  (Finset.univ.filter (fun t : BoolCube n => t i = false)).image
    (fun t => fun x => f i (cubeAddBool x t))

def c4Free {n : ℕ} (f : Fin n → BoolCube n → Prop) : Prop :=
  ∀ i j : Fin n, i < j → ∀ x : BoolCube n,
    x i = false → x j = false →
      ¬ (f i x ∧ f i (toggleBool x j) ∧
        f j x ∧ f j (toggleBool x i))

def firstSeven {n : ℕ} (hn : 7 ≤ n) (x : BoolCube n) : BoolCube 7 :=
  fun k => x ⟨k.1, lt_of_lt_of_le k.2 hn⟩

def liftedEdge {n : ℕ} (hn : 7 ≤ n)
    (i : Fin n) (x : BoolCube n) : Prop :=
  if h : i.1 < 7 then
    q7SeedSelected ⟨i.1, h⟩ (firstSeven hn x)
  else
    newSelected i x

def complementaryNewDirection {n : ℕ} (j : Fin n) : Prop :=
  ∀ i : Fin n, i ≠ j → ∀ x : BoolCube n,
    newParityFunction j (toggleBool x i) =
      Bool.not (newParityFunction j x)

def parityLiftEveryHigherCube_34966 : Prop :=
  q7SeedCertificate ∧
    (∀ n : ℕ, ∀ h : 7 < n,
      let hn : 7 ≤ n := Nat.le_of_lt h
      (∀ (i : Fin n) (h_i : i.1 < 7) (x : BoolCube n),
        liftedEdge hn i x =
          q7SeedSelected ⟨i.1, h_i⟩ (firstSeven hn x)) ∧
      (∀ (j : Fin n) (h_j : 7 ≤ j.1),
        directionalDensity (fun k x => newParityFunction k x) j = 1 / 2 ∧
        (translationOrbit (fun k x => newParityFunction k x) j).card = 2 ∧
        j.1 < n ∧ complementaryNewDirection j) ∧
      c4Free (liftedEdge hn))

end MathlibPlus.Open.Combinatorics.R1915
