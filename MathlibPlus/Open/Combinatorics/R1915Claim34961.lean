import Mathlib

namespace MathlibPlus.Open.Combinatorics.R1915Claim34961

noncomputable section

open Classical

abbrev Cube (n : ℕ) := Fin n → ZMod 2
abbrev Quotient3 := Fin 3 → ZMod 2

/-- The zero and coordinate-basis points in the Boolean base space. -/
def zeroCube {n : ℕ} : Cube n := fun _ => 0

def basisCube (n : ℕ) (j : Fin n) : Cube n :=
  fun k => if k = j then 1 else 0

/-- The affine-plane carrier of a three-point corner together with its fourth
point. -/
def affineCorner (A : Finset Quotient3) (b : Quotient3) : Prop :=
  A.card = 3 ∧
    b ∉ A ∧
      ∃ u v : Quotient3,
        u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
          A ∪ {b} = {b, b + u, b + v, b + u + v}

/-- The translated linear corner plane, based at the fourth point. -/
def cornerPlane (A : Finset Quotient3) (b : Quotient3) : Set Quotient3 :=
  {v | v = 0 ∨ ∃ a : Quotient3, a ∈ A ∧ v = a - b}

/-- A surjective affine quotient on the base points of direction `i`. -/
def affineQuotientOn {n : ℕ} (i : Fin n)
    (F : Cube n → Quotient3) : Prop :=
  ∃ L : Cube n →ₗ[ZMod 2] Quotient3, ∃ b : Quotient3,
    (∀ y : Quotient3, ∃ x : Cube n, x i = 0 ∧ F x = y) ∧
      (∀ x : Cube n, x i = 0 → F x = L x + b)

/-- The literal graph edge predicate is selected exactly outside the corner. -/
def selectedByCorner {n : ℕ} (i : Fin n)
    (F : Cube n → Quotient3) (A : Finset Quotient3)
    (E : Cube n → Prop) : Prop :=
  ∀ x : Cube n, x i = 0 → (E x ↔ F x ∉ A)

/-- The quotient displacement appearing on the `i,j` square. -/
def directionalDisplacement {n : ℕ}
    (F : Fin n → Cube n → Quotient3) (i j : Fin n) : Quotient3 :=
  F i (basisCube n j) - F i zeroCube

/-- The three autocorrelation values of the selected complement. -/
def quotientOppositeDensity
    (A : Finset Quotient3) (v : Quotient3) : ℚ :=
  ((Finset.univ.filter
      (fun y : Quotient3 => y ∉ A ∧ y + v ∉ A)).card : ℚ) / 8

/-- The common base points of an `i,j` coordinate square. -/
def squareBases (n : ℕ) (i j : Fin n) : Finset (Cube n) :=
  (Finset.univ : Finset (Cube n)).filter
    (fun x => x i = 0 ∧ x j = 0)

/-- The selected opposite pair in direction `i` on an `i,j` square. -/
def oppositePair {n : ℕ}
    (E : Fin n → Cube n → Prop) (i j : Fin n) : Set (Cube n) :=
  {x | x i = 0 ∧ x j = 0 ∧ E i x ∧ E i (x + basisCube n j)}

/-- Its literal density over the common square base space. -/
def oppositePairDensity {n : ℕ}
    (E : Fin n → Cube n → Prop) (i j : Fin n) : ℚ :=
  ((squareBases n i j).filter
      (fun x => E i x ∧ E i (x + basisCube n j))).card /
    (squareBases n i j).card

/-- Exact affine-quotient data for a family of missing-corner directions,
including the selected-edge carrier and the autocorrelation transfer. -/
def missingCornerData {n : ℕ} (H : Finset (Fin n))
    (F : Fin n → Cube n → Quotient3)
    (A : Fin n → Finset Quotient3)
    (E : Fin n → Cube n → Prop) : Prop :=
  (∀ i : Fin n, i ∈ H →
    affineQuotientOn i (F i) ∧
      affineCorner (A i) (F i zeroCube) ∧
        selectedByCorner i (F i) (A i) (E i)) ∧
  (∀ i : Fin n, i ∈ H → ∀ v : Quotient3,
    quotientOppositeDensity (A i) v =
      if v = 0 then (5 / 8 : ℚ)
      else if v ∈ cornerPlane (A i) (F i zeroCube) then (1 / 2 : ℚ)
      else (1 / 4 : ℚ)) ∧
  (∀ i : Fin n, i ∈ H → ∀ j : Fin n, j ∈ H → i ≠ j →
    oppositePairDensity E i j =
      quotientOppositeDensity (A i) (directionalDisplacement F i j))

/-- Literal `C₄`-freeness for the selected edge predicate on the cube. -/
def c4Free {n : ℕ} (E : Fin n → Cube n → Prop) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ x : Cube n,
    x i = 0 → x j = 0 →
      ¬ (E i x ∧ E i (x + basisCube n j) ∧
        E j x ∧ E j (x + basisCube n i))

def inPlaneNonzero {n : ℕ}
    (F : Fin n → Cube n → Quotient3)
    (A : Fin n → Finset Quotient3)
    (i : Fin n) (v : Quotient3) : Prop :=
  v ≠ 0 ∧ v ∈ cornerPlane (A i) (F i zeroCube)

/-- Disjointness of the two actual opposite-pair events forced by `C₄`-freeness. -/
def oppositePairDisjoint {n : ℕ}
    (E : Fin n → Cube n → Prop) (i j : Fin n) : Prop :=
  Disjoint (oppositePair E i j) (oppositePair E j i)

/-- Claim 34961: missing-corner displacements at a zero square have the
stated in-plane restriction, and a zero/in-plane pair is excluded by the
literal opposite-pair density obstruction. -/
def claim34961 : Prop :=
  ∀ (n : ℕ) (H : Finset (Fin n))
    (F : Fin n → Cube n → Quotient3)
    (A : Fin n → Finset Quotient3)
    (E : Fin n → Cube n → Prop),
    missingCornerData H F A E →
      c4Free E →
        (5 / 8 : ℚ) + 1 / 2 > 1 ∧
          (∀ i : Fin n, i ∈ H → ∀ j : Fin n, j ∈ H → i ≠ j →
            oppositePairDisjoint E i j) ∧
          (∀ i : Fin n, i ∈ H → ∀ j : Fin n, j ∈ H → i ≠ j →
            let v_ij := directionalDisplacement F i j
            let v_ji := directionalDisplacement F j i
            (inPlaneNonzero F A i v_ij ∨
                inPlaneNonzero F A j v_ji) ∧
              ¬ ((v_ij = 0 ∧ inPlaneNonzero F A j v_ji) ∨
                (v_ji = 0 ∧ inPlaneNonzero F A i v_ij)))

end

end MathlibPlus.Open.Combinatorics.R1915Claim34961
