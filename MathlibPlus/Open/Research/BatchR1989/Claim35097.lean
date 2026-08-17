import Mathlib

namespace MathlibPlus.Open.Research.BatchR1989

noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev F2_35097 := ZMod 2
abbrev Cube_35097 (n : ℕ) := Fin n → F2_35097
abbrev Face_35097 (n : ℕ) (i : Fin n) := {x : Cube_35097 n // x i = 0}

/-- The literal coordinate vector in the binary cube. -/
def cubeBasis_35097 (n : ℕ) (i : Fin n) : Cube_35097 n :=
  fun j => if j = i then 1 else 0

/-- Exact quotient data for one coordinate function.  The map is onto its
binary quotient, kills the deleted coordinate, and represents the selected
function on the coordinate-vanishing face. -/
def exactQuotientRepresentation_35097 {n : ℕ} {i : Fin n}
    {W : Type*} [AddCommGroup W] [Module F2_35097 W]
    (g : Face_35097 n i → F2_35097)
    (F : Cube_35097 n →ₗ[F2_35097] W) (S : Set W) : Prop :=
  Function.Surjective F ∧
    F (cubeBasis_35097 n i) = 0 ∧
    ∀ x : Face_35097 n i,
      g x = if F x.1 ∈ S then 1 else 0

/-- Joint image on the pair face `x_(I i)=x_(I j)=0`. -/
def pairImage_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (i j : Fin h) : Set (W i × W j) :=
  {p | ∃ x : Cube_35097 n,
    x (I i) = 0 ∧ x (I j) = 0 ∧ (F i x, F j x) = p}

/-- Joint image after also imposing the third coordinate to be zero. -/
def tripleImage_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (i j k : Fin h) : Set ((W i × W j) × W k) :=
  {p | ∃ x : Cube_35097 n,
    x (I i) = 0 ∧ x (I j) = 0 ∧ x (I k) = 0 ∧
      ((F i x, F j x), F k x) = p}

/-- The `i,j` projection of a triple image. -/
def triplePairImage_ij_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (i j k : Fin h) : Set (W i × W j) :=
  {p | ∃ z : W k, (p, z) ∈ tripleImage_35097 I F i j k}

/-- The `i,k` projection of a triple image. -/
def triplePairImage_ik_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (i j k : Fin h) : Set (W i × W k) :=
  {p | ∃ y : W j, ((p.1, y), p.2) ∈ tripleImage_35097 I F i j k}

/-- The `j,k` projection of a triple image. -/
def triplePairImage_jk_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (i j k : Fin h) : Set (W j × W k) :=
  {p | ∃ x : W i, ((x, p.1), p.2) ∈ tripleImage_35097 I F i j k}

/-- A triple is bad when one of its three pair projections is not the
corresponding undeleted pair image. -/
def badTriple_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (i j k : Fin h) : Prop :=
  triplePairImage_ij_35097 I F i j k ≠ pairImage_35097 I F i j ∨
    triplePairImage_ik_35097 I F i j k ≠ pairImage_35097 I F i k ∨
    triplePairImage_jk_35097 I F i j k ≠ pairImage_35097 I F j k

/-- Ordered triples represent the unordered triples of directions once. -/
def orderedTriples_35097 (h : ℕ) :
    Finset ((Fin h × Fin h) × Fin h) :=
  Finset.univ.filter (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2)

/-- The defective third coordinates for a fixed ordered pair. -/
def defectiveThirds_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (i j : Fin h) : Finset (Fin h) :=
  (Finset.univ.filter (fun k =>
    k ≠ i ∧ k ≠ j ∧
      triplePairImage_ij_35097 I F i j k ≠ pairImage_35097 I F i j))

/-- The number of bad ordered triples surviving in a selected direction set. -/
def survivingBadTriples_35097 {n h : ℕ}
    {W : Fin h → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module F2_35097 (W i)]
    (I : Fin h → Fin n)
    (F : ∀ i, Cube_35097 n →ₗ[F2_35097] W i)
    (R : Finset (Fin h)) : Finset ((Fin h × Fin h) × Fin h) :=
  (orderedTriples_35097 h).filter (fun t =>
    t.1.1 ∈ R ∧ t.1.2 ∈ R ∧ t.2 ∈ R ∧
      badTriple_35097 I F t.1.1 t.1.2 t.2)

/-- The product mass of a finite subset under independent Bernoulli
selection with parameter `p`. -/
def independentSelectionMass_35097 {h : ℕ}
    (p : ℝ) (R : Finset (Fin h)) : ℝ :=
  p ^ R.card * (1 - p) ^ (h - R.card)

/-- Claim 35097: exact quotient ranks give the fixed-pair defect bound, the
bad-triple count, and the independent-selection/deletion extraction. -/
def claim_35097 : Prop :=
  ∀ {n h r : ℕ}
    (I : Fin h → Fin n)
    (W : Fin h → Type*)
    [∀ i, Fintype (W i)]
    [∀ i, AddCommGroup (W i)]
    [∀ i, Module F2_35097 (W i)]
    [∀ i, FiniteDimensional F2_35097 (W i)]
    (g : ∀ i : Fin h, Face_35097 n (I i) → F2_35097)
    (F : ∀ i : Fin h, Cube_35097 n →ₗ[F2_35097] W i)
    (S : ∀ i : Fin h, Set (W i)),
    Function.Injective I →
    (∀ i, exactQuotientRepresentation_35097 (g i) (F i) (S i)) →
    (∀ i, Module.finrank F2_35097 (W i) ≤ r) →
    let B :=
      ((orderedTriples_35097 h).filter (fun t =>
        badTriple_35097 I F t.1.1 t.1.2 t.2)).card
    (∀ i j : Fin h, i ≠ j →
        (defectiveThirds_35097 I F i j).card ≤ 2 * r) ∧
      B ≤ 2 * r * Nat.choose h 2 ∧
      2 * r * Nat.choose h 2 ≤ r * h ^ 2 ∧
      (r = 0 →
        ∀ t ∈ orderedTriples_35097 h,
          ¬ badTriple_35097 I F t.1.1 t.1.2 t.2) ∧
      (r ≠ 0 →
        (h = 0 ∧
          ∃ J : Finset (Fin h),
            J.card ≥ 0 ∧
            ∀ t ∈ orderedTriples_35097 h,
              t.1.1 ∈ J → t.1.2 ∈ J → t.2 ∈ J →
                ¬ badTriple_35097 I F t.1.1 t.1.2 t.2) ∨
        (0 < h ∧
          let p : ℝ :=
            Real.rpow (3 * (r : ℝ) * (h : ℝ)) ((-1 : ℝ) / 2)
          ∃ R : Finset (Fin h),
            0 < independentSelectionMass_35097 p R ∧
            ∃ J : Finset (Fin h),
              (∀ x ∈ J, x ∈ R) ∧
              R.card - J.card ≤
                (survivingBadTriples_35097 I F R).card ∧
              J.card ≥ Nat.floor
                ((2 : ℝ) / (3 * Real.sqrt 3) *
                  Real.sqrt ((h : ℝ) / (r : ℝ))) ∧
              ∀ t ∈ orderedTriples_35097 h,
                t.1.1 ∈ J → t.1.2 ∈ J → t.2 ∈ J →
                  ¬ badTriple_35097 I F t.1.1 t.1.2 t.2))

end
end MathlibPlus.Open.Research.BatchR1989
