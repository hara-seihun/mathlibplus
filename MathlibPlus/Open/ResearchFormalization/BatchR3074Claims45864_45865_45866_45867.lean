import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR3074

noncomputable section

abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Omega (d n : ℕ) := V d × Fin n

/-- The diagonal affine permutation carrier `M ⋊ (GL(V) × S_n)`. -/
def diagonalAffineForm {d n : ℕ}
    (f : Equiv.Perm (Omega d n)) : Prop :=
  ∃ (L : V d ≃+ V d) (t : V d) (σ : Equiv.Perm (Fin n)),
    ∀ x : V d, ∀ i : Fin n,
      f (x, i) = (L x + t, σ i)

def diagonalAffineSet (d n : ℕ) : Set (Equiv.Perm (Omega d n)) :=
  {f | diagonalAffineForm f}

def diagonalAffineGroup (d n : ℕ) :
    Subgroup (Equiv.Perm (Omega d n)) :=
  Subgroup.closure (diagonalAffineSet d n)

def diagonalTranslationForm {d n : ℕ}
    (f : Equiv.Perm (Omega d n)) : Prop :=
  ∃ t : V d, ∀ x : V d, ∀ i : Fin n,
    f (x, i) = (x + t, i)

def diagonalTranslationSet (d n : ℕ) : Set (Equiv.Perm (Omega d n)) :=
  {f | diagonalTranslationForm f}

def diagonalTranslationGroup (d n : ℕ) :
    Subgroup (Equiv.Perm (Omega d n)) :=
  Subgroup.closure (diagonalTranslationSet d n)

def blockSet (d n : ℕ) (i : Fin n) : Set (Omega d n) :=
  {x | x.2 = i}

def blockPartition (d n : ℕ) : Prop :=
  (∀ x : Omega d n, ∃! i : Fin n, x ∈ blockSet d n i)

def affineLocalPermSet (d : ℕ) : Set (Equiv.Perm (V d)) :=
  {g | ∃ (L : V d ≃+ V d) (t : V d),
    ∀ x : V d, g x = L x + t}

def localPermSet (d n : ℕ) (i : Fin n) : Set (Equiv.Perm (V d)) :=
  {g | ∃ f : Equiv.Perm (Omega d n), diagonalAffineForm f ∧
    ∀ x : V d, f (x, i) = (g x, i)}

def translationPerm (d : ℕ) (t : V d) : Equiv.Perm (V d) :=
  Equiv.addRight t

def affineBlockForLocalAction (d : ℕ) (C : Set (V d)) : Prop :=
  C.Nonempty ∧ 0 ∈ C ∧
    ∀ g : Equiv.Perm (V d), g ∈ affineLocalPermSet d →
      Set.image g C = C ∨ Disjoint (Set.image g C) C

def affineLocalGroup (d : ℕ) : Subgroup (Equiv.Perm (V d)) :=
  Subgroup.closure (affineLocalPermSet d)

def localTranslationGroup (d : ℕ) : Subgroup (Equiv.Perm (V d)) :=
  Subgroup.closure {g | ∃ t : V d, g = translationPerm d t}

def normalIn {X : Type*} [Group X] (N K : Subgroup X) : Prop :=
  ∀ k : K, ∀ n : N, k.1 * n.1 * k.1⁻¹ ∈ N

def localTranslationSocle (d : ℕ) : Prop :=
  localTranslationGroup d ≤ affineLocalGroup d ∧
    normalIn (localTranslationGroup d) (affineLocalGroup d) ∧
    localTranslationGroup d ≠ ⊥ ∧
    ∀ N : Subgroup (Equiv.Perm (V d)),
      N ≤ localTranslationGroup d → normalIn N (affineLocalGroup d) →
        N = ⊥ ∨ N = localTranslationGroup d

def localTranslationNormalizer (d : ℕ) : Prop :=
  ∀ (g : Equiv.Perm (V d)), g ∈ affineLocalPermSet d →
    ∀ t : V d, ∃ t' : V d,
      g * translationPerm d t * g⁻¹ = translationPerm d t'

def subgroupOrbit {X : Type*}
    (K : Subgroup (Equiv.Perm X)) (x : X) : Set X :=
  {y | ∃ g : K, g.1 x = y}

def pairProjection {d n : ℕ} (i j : Fin n) : Set (V d × V d) :=
  {p | ∃ g : diagonalTranslationGroup d n,
    p = ((g.1 (0, i)).1, (g.1 (0, j)).1)}

def pairIncidenceMatrix (d : ℕ) :
    Matrix (Fin d) (Fin (2 * d)) (ZMod 2) :=
  fun i j =>
    if h : j.val < d then
      if i.val = j.val then 1 else 0
    else
      if i.val = j.val - d then 1 else 0

def pairIncidenceRank (d : ℕ) : Prop :=
  Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.mulVecLin (pairIncidenceMatrix d))) = d

/-- Claim 45864: the explicit diagonal affine group is transitive, has the
literal invariant blocks, and induces all of S_n on those blocks. -/
def transitivityAndBlockQuotient_claim45864 : Prop :=
  ∀ (d n : ℕ), 2 ≤ d → 3 ≤ n →
    (∀ x y : Omega d n, ∃ f : Equiv.Perm (Omega d n),
      diagonalAffineForm f ∧ f x = y) ∧
    blockPartition d n ∧
    (∀ f : Equiv.Perm (Omega d n), diagonalAffineForm f →
      ∀ i : Fin n, ∃ j : Fin n, ∀ x : V d,
        (f (x, i)).2 = j) ∧
    (∀ σ : Equiv.Perm (Fin n), ∃ f : Equiv.Perm (Omega d n),
      diagonalAffineForm f ∧
        ∀ x : V d, ∀ i : Fin n,
          f (x, i) = (x, σ i))

/-- Claim 45865: each block stabilizer gives the full primitive affine local
action, with the diagonal translation subgroup as its translation socle. -/
def primitiveAffineLocalAction_claim45865 : Prop :=
  ∀ (d n : ℕ), 2 ≤ d → 3 ≤ n → ∀ i : Fin n,
    localPermSet d n i = affineLocalPermSet d ∧
    (∀ C : Set (V d), affineBlockForLocalAction d C →
      C = Set.univ ∨ C.Subsingleton) ∧
    (∀ t : V d, translationPerm d t ∈ localPermSet d n i) ∧
    localTranslationNormalizer d ∧ localTranslationSocle d

/-- Minimality among actual normal subgroups, not arbitrary invariant subsets. -/
def minimalNormalTranslationLayer (d n : ℕ) : Prop :=
  diagonalTranslationGroup d n ≠ ⊥ ∧
    diagonalTranslationGroup d n ≤ diagonalAffineGroup d n ∧
    normalIn (diagonalTranslationGroup d n) (diagonalAffineGroup d n) ∧
    ∀ N : Subgroup (Equiv.Perm (Omega d n)),
      N ≤ diagonalTranslationGroup d n →
        normalIn N (diagonalAffineGroup d n) →
          N = ⊥ ∨ N = diagonalTranslationGroup d n

/-- Claim 45866: the diagonal translation layer is a minimal nontrivial normal
subgroup in the block kernel, its block orbits are full blocks, and its two
block projections are diagonal rather than full. -/
def minimalNormalDiagonalLayer_claim45866 : Prop :=
  ∀ (d n : ℕ), 2 ≤ d → 3 ≤ n →
    minimalNormalTranslationLayer d n ∧
    (∀ g : diagonalTranslationGroup d n, ∀ x : Omega d n,
      (g.1 x).2 = x.2) ∧
    (∀ i : Fin n, ∀ x : V d,
      subgroupOrbit (diagonalTranslationGroup d n) (x, i) =
        blockSet d n i) ∧
    (∀ i : Fin n, ∀ v : V d, ∃ g : diagonalTranslationGroup d n,
      (g.1 (0, i)).1 = v) ∧
    (∀ i j : Fin n, i ≠ j →
      pairProjection (d := d) i j = {(v, v) | v : V d} ∧
      Set.ncard (pairProjection (d := d) i j) = 2 ^ d ∧
      2 ^ d < 2 ^ (2 * d)) ∧
    pairIncidenceRank d

/-- Claim 45867: no proper nontrivial affine block refinement exists inside a
block, and the corresponding GL(V)-invariant subspaces are only 0 and V. -/
def noProperInvariantLocalRefinement_claim45867 : Prop :=
  ∀ (d n : ℕ), 2 ≤ d → 3 ≤ n →
    (∀ C : Set (V d), affineBlockForLocalAction d C →
      C = Set.univ ∨ C = ({0} : Set (V d))) ∧
    (∀ W : Submodule (ZMod 2) (V d),
      (∀ L : V d ≃+ V d, ∀ x : V d, x ∈ W → L x ∈ W) →
        W = ⊥ ∨ W = ⊤)

end
end MathlibPlus.Open.ResearchFormalization.BatchR3074
