import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Geometry.GridBatch

open Filter

abbrev Point := Fin 2 → ℝ

def dot (u v : Point) : ℝ :=
  ∑ c : Fin 2, u c * v c

def sqNorm (u : Point) : ℝ := dot u u

def sqDistance (u v : Point) : ℝ := sqNorm (u - v)

def Pair (V : Type*) [LinearOrder V] := {p : V × V // p.1 < p.2}

instance pairFinite {V : Type*} [LinearOrder V] [Fintype V] :
    Finite (Pair V) :=
  Finite.of_injective (fun p : Pair V => p.1) Subtype.val_injective

noncomputable instance pairFintype {V : Type*} [LinearOrder V] [Fintype V] :
    Fintype (Pair V) := Fintype.ofFinite _

noncomputable def qmax {V : Type*} [LinearOrder V] [Fintype V]
    (X : V → Point) : ℝ :=
  sSup {r : ℝ | ∃ p : Pair V,
    sqDistance (X p.1.1) (X p.1.2) = r}

def unitVector (u : Point) : Prop := sqNorm u = 1

def nonparallel (u v : Point) : Prop :=
  u 0 * v 1 - u 1 * v 0 ≠ 0

def gridPoint {p q : ℕ} (u v : Point)
    (ij : Fin (p + 1) × Fin (q + 1)) : Point :=
  (ij.1.val : ℝ) • u + (ij.2.val : ℝ) • v

def gridPointMap {p q : ℕ} (u v : Point) :
    Fin (p + 1) × Fin (q + 1) → Point :=
  gridPoint u v

def gridContained {n p q : ℕ} (X : Fin n → Point)
    (u v : Point) : Prop :=
  ∃ e : (Fin (p + 1) × Fin (q + 1)) → Fin n,
    Function.Injective e ∧ ∀ ij, X (e ij) = gridPoint u v ij

def finEmbed {p : ℕ} (i : Fin p) : Fin (p + 1) :=
  ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self p)⟩

def finSucc {p : ℕ} (i : Fin p) : Fin (p + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def gridEdgesUnit {p q : ℕ} (u v : Point) : Prop :=
  (∀ i : Fin p, ∀ j : Fin (q + 1),
    sqDistance
        (gridPoint u v (finEmbed i, j))
        (gridPoint u v (finSucc i, j)) = 1) ∧
  (∀ i : Fin (p + 1), ∀ j : Fin q,
    sqDistance
        (gridPoint u v (i, finEmbed j))
        (gridPoint u v (i, finSucc j)) = 1)

/-- Claim 40411: the complete unit parallelogram grid is the stated grid
contained in an n-point planar configuration, with no additional graph or
optimization hypotheses. -/
def claim40411 : Prop :=
  ∀ (n p q : ℕ) (X : Fin n → Point) (u v : Point),
    1 ≤ p → 1 ≤ q → Function.Injective X →
      unitVector u → unitVector v → nonparallel u v →
      gridContained (p := p) (q := q) X u v →
        Function.Injective (gridPointMap (p := p) (q := q) u v) ∧
          Fintype.card (Fin (p + 1) × Fin (q + 1)) =
            (p + 1) * (q + 1) ∧
          gridEdgesUnit (p := p) (q := q) u v

def oneSeparated {V : Type*} (X : V → Point) : Prop :=
  ∀ i j, i ≠ j → 1 ≤ sqDistance (X i) (X j)

def globalDiameterMinimizer {n : ℕ} (X : Fin n → Point) : Prop :=
  oneSeparated X ∧
    ∀ Y : Fin n → Point, oneSeparated Y → qmax X ≤ qmax Y

def outsideCount (n p q : ℕ) : ℕ := n - (p + 1) * (q + 1)

/-- Claim 40413: the unrestricted planar comparison and the grid-corner lower
bound give the exact all-order density and outside-point inequalities. -/
def claim40413 : Prop :=
  ∀ (n p q : ℕ) (X : Fin n → Point) (u v : Point),
    1 ≤ p → 1 ≤ q → Function.Injective X →
      unitVector u → unitVector v → nonparallel u v →
      globalDiameterMinimizer X →
        gridContained (p := p) (q := q) X u v →
        qmax X ≤ (2 * Real.sqrt 3 / Real.pi) * (n : ℝ) ∧
          (2 * p * q : ℝ) ≤ qmax X ∧
          (n : ℝ) ≥ (Real.pi / Real.sqrt 3) * p * q ∧
          (outsideCount n p q : ℝ) ≥
            (Real.pi / Real.sqrt 3 - 1) * p * q - p - q - 1

def gridSequenceData
    (p q n : ℕ → ℕ)
    (u v : ℕ → Point)
    (X : ∀ k : ℕ, Fin (n k) → Point) : Prop :=
  ∀ k,
    1 ≤ p k ∧ 1 ≤ q k ∧ 1 ≤ n k ∧
      Function.Injective (X k) ∧
      unitVector (u k) ∧ unitVector (v k) ∧
      nonparallel (u k) (v k) ∧
      globalDiameterMinimizer (X k) ∧
      gridContained (p := p k) (q := q k) (X k) (u k) (v k)

def minTendsToInfinity (p q : ℕ → ℕ) : Prop :=
  ∀ B : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → B ≤ p k ∧ B ≤ q k

def outsideIsLinearOrder
    (p q n : ℕ → ℕ) : Prop :=
  ∃ C K : ℕ, ∀ k, K ≤ k →
    outsideCount (n k) (p k) (q k) ≤ C * (p k + q k)

/-- Claim 40414: along increasingly wide optimal grids, the boundary term
vanishes in the density ratio, leaving the stated limiting grid fraction and
outside fraction; linear-size outside mass is impossible. -/
def claim40414 : Prop :=
  ∀ (p q n : ℕ → ℕ)
    (u v : ℕ → Point)
    (X : ∀ k : ℕ, Fin (n k) → Point),
    gridSequenceData p q n u v X →
      minTendsToInfinity p q →
        (∀ k,
          (((p k + 1) * (q k + 1) : ℕ) : ℝ) / (n k : ℝ) ≤
            Real.sqrt 3 / Real.pi +
              ((p k + q k + 1 : ℕ) : ℝ) / (n k : ℝ)) ∧
          (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
            1 - (((p k + 1) * (q k + 1) : ℕ) : ℝ) / (n k : ℝ) ≥
              1 - Real.sqrt 3 / Real.pi - ε) ∧
          ¬ outsideIsLinearOrder p q n

end MathlibPlus.Open.Geometry.GridBatch
