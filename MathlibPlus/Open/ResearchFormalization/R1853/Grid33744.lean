import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1853

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev GridPlane := Fin 2 → ℝ
abbrev GridVertex (p q : ℕ) := Fin (p + 1) × Fin (q + 1)

inductive GridStressEdge (p q : ℕ) where
  | horizontal (i : Fin p) (j : Fin (q + 1))
  | vertical (i : Fin (p + 1)) (j : Fin q)
  deriving DecidableEq, Fintype

abbrev BoundaryGridStressEdge (p q : ℕ) :=
  {e : GridStressEdge p q //
    match e with
    | .horizontal _ j => j = 0 ∨ j = Fin.last q
    | .vertical i _ => i = 0 ∨ i = Fin.last p}

abbrev GridInteriorRowIndex (q : ℕ) :=
  {j : Fin (q + 1) // 0 < j.val ∧ j.val < q}
abbrev GridInteriorColumnIndex (p : ℕ) :=
  {i : Fin (p + 1) // 0 < i.val ∧ i.val < p}
abbrev GridChordIndex (p q : ℕ) :=
  GridInteriorRowIndex q ⊕ GridInteriorColumnIndex p
abbrev CondensedGridStressEdge (p q : ℕ) :=
  BoundaryGridStressEdge p q ⊕ GridChordIndex p q

def gridStressEndpoints {p q : ℕ}
    (e : GridStressEdge p q) : GridVertex p q × GridVertex p q :=
  match e with
  | .horizontal i j => ((i.castSucc, j), (i.succ, j))
  | .vertical i j => ((i, j.castSucc), (i, j.succ))

def gridStressDirection {p q : ℕ}
    (u v : GridPlane) (e : GridStressEdge p q) : GridPlane :=
  match e with
  | .horizontal _ _ => u
  | .vertical _ _ => v

def gridStressWeight {p q : ℕ}
    (a b : ℕ → ℕ → ℝ) (e : GridStressEdge p q) : ℝ :=
  match e with
  | .horizontal i j => a i.val j.val
  | .vertical i j => b i.val j.val

def gridStressForceAt {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ)
    (e : GridStressEdge p q) (x : GridVertex p q) : GridPlane :=
  if x = (gridStressEndpoints e).1 then
    -(gridStressWeight a b e) • gridStressDirection u v e
  else if x = (gridStressEndpoints e).2 then
    (gridStressWeight a b e) • gridStressDirection u v e
  else 0

def gridStressOuter (w : GridPlane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => w i * w j

def gridStressMomentTerm {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ)
    (e : GridStressEdge p q) : Matrix (Fin 2) (Fin 2) ℝ :=
  (gridStressWeight a b e) • gridStressOuter (gridStressDirection u v e)

def gridStressForce {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ)
    (x : GridVertex p q) : GridPlane :=
  ∑ e : GridStressEdge p q, gridStressForceAt u v a b e x

def gridStressMoment {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ e : GridStressEdge p q, gridStressMomentTerm u v a b e

def interiorGridForceBalance {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ) : Prop :=
  ∀ i j : ℕ, 0 < i → i < p → 0 < j → j < q →
    (a (i - 1) j - a i j) • u +
      (b i (j - 1) - b i j) • v = 0

def horizontalInteriorRowConstancy {p q : ℕ}
    (a : ℕ → ℕ → ℝ) : Prop :=
  ∀ j, 0 < j → j < q →
    ∀ i₁ i₂, i₁ < p → i₂ < p → a i₁ j = a i₂ j

def verticalInteriorColumnConstancy {p q : ℕ}
    (b : ℕ → ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i < p →
    ∀ j₁ j₂, j₁ < q → j₂ < q → b i j₁ = b i j₂

def gridDirectionsIndependent (u v : GridPlane) : Prop :=
  ∀ A B : ℝ, A • u + B • v = 0 → A = 0 ∧ B = 0

def gridUnitDirection (w : GridPlane) : Prop :=
  ∑ k : Fin 2, (w k) ^ 2 = 1

def interiorGridRowIndex {q : ℕ} (j : GridInteriorRowIndex q) : Fin (q + 1) :=
  j.1

def interiorGridColumnIndex {p : ℕ} (i : GridInteriorColumnIndex p) : Fin (p + 1) :=
  i.1

def condensedGridEndpoints {p q : ℕ}
    (e : CondensedGridStressEdge p q) : GridVertex p q × GridVertex p q :=
  match e with
  | Sum.inl boundary => gridStressEndpoints boundary.1
  | Sum.inr (Sum.inl j) =>
      ((0, interiorGridRowIndex j), (Fin.last p, interiorGridRowIndex j))
  | Sum.inr (Sum.inr i) =>
      ((interiorGridColumnIndex i, 0),
        (interiorGridColumnIndex i, Fin.last q))

def condensedGridDirection {p q : ℕ}
    (u v : GridPlane) (e : CondensedGridStressEdge p q) : GridPlane :=
  match e with
  | Sum.inl boundary => gridStressDirection u v boundary.1
  | Sum.inr (Sum.inl _) => (p : ℝ) • u
  | Sum.inr (Sum.inr _) => (q : ℝ) • v

def condensedGridWeight {p q : ℕ}
    (a b : ℕ → ℕ → ℝ) (e : CondensedGridStressEdge p q) : ℝ :=
  match e with
  | Sum.inl boundary => gridStressWeight a b boundary.1
  | Sum.inr (Sum.inl j) => a 0 j.val / (p : ℝ)
  | Sum.inr (Sum.inr i) => b i.val 0 / (q : ℝ)

def condensedGridForceAt {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ)
    (e : CondensedGridStressEdge p q) (x : GridVertex p q) : GridPlane :=
  if x = (condensedGridEndpoints e).1 then
    -(condensedGridWeight a b e) • condensedGridDirection u v e
  else if x = (condensedGridEndpoints e).2 then
    (condensedGridWeight a b e) • condensedGridDirection u v e
  else 0

def condensedGridMomentTerm {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ)
    (e : CondensedGridStressEdge p q) : Matrix (Fin 2) (Fin 2) ℝ :=
  (condensedGridWeight a b e) •
    gridStressOuter (condensedGridDirection u v e)

def condensedGridForce {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ)
    (x : GridVertex p q) : GridPlane :=
  ∑ e : CondensedGridStressEdge p q, condensedGridForceAt u v a b e x

def condensedGridMoment {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ e : CondensedGridStressEdge p q, condensedGridMomentTerm u v a b e

def gridStressNonnegative {p q : ℕ}
    (a b : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, i < p → j ≤ q → 0 ≤ a i j) ∧
    (∀ i j, i ≤ p → j < q → 0 ≤ b i j)

def condensedGridEnergy {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e : CondensedGridStressEdge p q,
    condensedGridWeight a b e *
      ∑ k : Fin 2, (condensedGridDirection u v e k) ^ 2

def gridStressEnergy {p q : ℕ}
    (u v : GridPlane) (a b : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e : GridStressEdge p q,
    gridStressWeight a b e *
      ∑ k : Fin 2, (gridStressDirection u v e k) ^ 2

def matrixTrace2 (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ k : Fin 2, M k k

/-- Boundary edges are retained with their original stresses; only the
p+q-2 interior row and column families become one-oriented boundary chords. -/
def parallelogramGridBoundaryCondensation_claim33744 : Prop :=
  ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q →
    ∀ (u v : GridPlane), gridDirectionsIndependent u v →
      ∀ (a b : ℕ → ℕ → ℝ),
        interiorGridForceBalance (p := p) (q := q) u v a b →
          horizontalInteriorRowConstancy (p := p) (q := q) a ∧
          verticalInteriorColumnConstancy (p := p) (q := q) b ∧
          Fintype.card (GridChordIndex p q) = p + q - 2 ∧
          (∀ x : GridVertex p q,
            gridStressForce (p := p) (q := q) u v a b x =
              condensedGridForce (p := p) (q := q) u v a b x) ∧
          gridStressMoment (p := p) (q := q) u v a b =
            condensedGridMoment (p := p) (q := q) u v a b ∧
          ((gridUnitDirection u ∧ gridUnitDirection v) →
            gridStressEnergy (p := p) (q := q) u v a b =
                condensedGridEnergy (p := p) (q := q) u v a b ∧
            matrixTrace2 (gridStressMoment (p := p) (q := q) u v a b) =
              matrixTrace2 (condensedGridMoment (p := p) (q := q) u v a b)) ∧
          (gridStressNonnegative (p := p) (q := q) a b →
            ∀ e : CondensedGridStressEdge p q,
              0 ≤ condensedGridWeight a b e)

end
end MathlibPlus.Open.ResearchFormalization.R1853
