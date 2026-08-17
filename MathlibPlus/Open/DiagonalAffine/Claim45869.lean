import Mathlib

noncomputable section

namespace MathlibPlus.Open.DiagonalAffine

abbrev Vector (d : ℕ) := Fin d → ZMod 2
abbrev Point (d n : ℕ) := Vector d × Fin n

def diagonalTranslation {d n : ℕ} (v : Vector d) : Point d n → Point d n :=
  fun p => (p.1 + v, p.2)

def diagonalAffineMap {d n : ℕ} (v : Vector d)
    (A : Vector d ≃ₗ[ZMod 2] Vector d) (σ : Equiv.Perm (Fin n)) :
    Point d n → Point d n :=
  fun p => (A p.1 + v, σ p.2)

def translationLayer (d n : ℕ) : Set (Point d n → Point d n) :=
  {f | ∃ v : Vector d, f = diagonalTranslation v}

def diagonalAffineLayer (d n : ℕ) : Set (Point d n → Point d n) :=
  {f | ∃ (v : Vector d) (A : Vector d ≃ₗ[ZMod 2] Vector d)
      (σ : Equiv.Perm (Fin n)), f = diagonalAffineMap v A σ}

def block (d n : ℕ) (i : Fin n) : Set (Point d n) :=
  {p | p.2 = i}

def invertibleMatrices (d : ℕ) : Set (Matrix (Fin d) (Fin d) (ZMod 2)) :=
  {A | ∃ B, A * B = 1 ∧ B * A = 1}

def invariantVectorSubspace (d : ℕ)
    (W : Submodule (ZMod 2) (Vector d)) : Prop :=
  ∀ (A : Vector d ≃ₗ[ZMod 2] Vector d) (x : Vector d),
    x ∈ W → A x ∈ W

def glInvariantSubspaceSizes39 : Set ℕ :=
  {m | ∃ W : Submodule (ZMod 2) (Vector 3),
    invariantVectorSubspace 3 W ∧ m = Set.ncard (W : Set (Vector 3))}

def equalityIncidence (d : ℕ) :
    Matrix (Fin d) (Fin d ⊕ Fin d) (ZMod 2) :=
  fun i j => match j with
    | Sum.inl k => if i = k then 1 else 0
    | Sum.inr k => if i = k then 1 else 0

def incidenceColumnSpan (d : ℕ) :
    Submodule (ZMod 2) (Fin d → ZMod 2) :=
  Submodule.span (ZMod 2)
    (Set.range
      (fun j : Fin d ⊕ Fin d =>
        fun i : Fin d => equalityIncidence d i j))

def incidenceRank (d : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (incidenceColumnSpan d)

def singleBlockProjection (d n : ℕ) (i : Fin n) : Set (Vector d) :=
  {v | ∃ f, f ∈ translationLayer d n ∧ (f (0, i)).1 = v}

def twoBlockProjection (d n : ℕ) (i j : Fin n) :
    Set (Vector d × Vector d) :=
  {p | ∃ f, f ∈ translationLayer d n ∧
    p = ((f (0, i)).1, (f (0, j)).1)}

def fullTwoBlockProduct (d n : ℕ) (i j : Fin n) :
    Set (Vector d × Vector d) :=
  {p | p.1 ∈ singleBlockProjection d n i ∧
    p.2 ∈ singleBlockProjection d n j}

def diagonalPairs (d : ℕ) : Set (Vector d × Vector d) :=
  {p | p.1 = p.2}

def xTransitive (d n : ℕ) : Prop :=
  ∀ p q : Point d n, ∃ f,
    f ∈ diagonalAffineLayer d n ∧ f p = q

def blockQuotientTwoTransitive (n : ℕ) : Prop :=
  ∀ a b c d : Fin n, a ≠ b → c ≠ d →
    ∃ f, f ∈ diagonalAffineLayer 3 n ∧
      (∀ x : Vector 3,
        (f (x, a)).2 = c ∧ (f (x, b)).2 = d)

def permutationSubgroup {α : Type*} (K : Set (α → α)) : Prop :=
  (∀ f ∈ K, Function.Bijective f) ∧
    id ∈ K ∧
    (∀ f ∈ K, ∀ g ∈ K, f ∘ g ∈ K) ∧
    (∀ f ∈ K, ∃ g ∈ K,
      ∀ x, f (g x) = x ∧ g (f x) = x)

def regularOn {α : Type*} (K : Set (α → α)) : Prop :=
  permutationSubgroup K ∧
    ∀ p q : α, ∃! f, f ∈ K ∧ f p = q

def cyclicBlockShift (h : ZMod 9) (i : Fin 9) : Fin 9 :=
  Fin.ofNat 9 (i.val + h.val)

def targetRegularLayer : Set (Point 3 9 → Point 3 9) :=
  {f | ∃ v : Vector 3, ∃ h : ZMod 9,
    ∀ p, f p = (p.1 + v, cyclicBlockShift h p.2)}

/-- The exact finite replay at `d = 3`, `n = 9`, with the diagonal
translation layer, common linear action, block permutation action, the two
projection carriers, the binary incidence matrix, the invariant-subspace
sizes, and the concrete regular `C₂^3 × C₉` target layer all retained. -/
def claim45869_exact_d3_n9_replay : Prop :=
  Set.ncard (invertibleMatrices 3) = 168 ∧
  Set.ncard (translationLayer 3 9) = 8 ∧
  Set.ncard (block 3 9 0) = 8 ∧
  Fintype.card (Fin 9) = 9 ∧
  Fintype.card (Point 3 9) = 72 ∧
  Set.ncard (singleBlockProjection 3 9 0) = 8 ∧
  Set.ncard (twoBlockProjection 3 9 0 1) = 8 ∧
  Set.ncard (fullTwoBlockProduct 3 9 0 1) = 64 ∧
  twoBlockProjection 3 9 0 1 = diagonalPairs 3 ∧
  incidenceRank 3 = 3 ∧
  glInvariantSubspaceSizes39 = ({1, 8} : Set ℕ) ∧
  xTransitive 3 9 ∧
  blockQuotientTwoTransitive 9 ∧
  regularOn targetRegularLayer ∧
  Set.ncard targetRegularLayer = 72 ∧
  targetRegularLayer ⊆ diagonalAffineLayer 3 9

end MathlibPlus.Open.DiagonalAffine

end
