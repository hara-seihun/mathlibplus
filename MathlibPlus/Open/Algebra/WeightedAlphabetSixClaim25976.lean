import Mathlib
import MathlibPlus.Algebra.Claim6218

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976

noncomputable section

/-- The finite interval `{0, ..., N}` used by the annihilator coordinates. -/
def Index (N : ℕ) := {t : ℕ // t ≤ N}

/-- A nonnegative six-part composition of the fixed total `N`. -/
def Composition (m N : ℕ) := {μ : Fin m → ℕ // ∑ i, μ i = N}

def zeroIndex (N : ℕ) : Index N := ⟨0, Nat.zero_le _⟩

def reflectIndex (N : ℕ) (t : Index N) : Index N :=
  ⟨N - t.1, Nat.sub_le _ _⟩

def subsetIndex {m N : ℕ} (μ : Composition m N) (I : Finset (Fin m)) : Index N :=
  ⟨∑ i ∈ I, μ.1 i, by
    calc
      ∑ i ∈ I, μ.1 i ≤ ∑ i : Fin m, μ.1 i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ I)
      _ = N := μ.2⟩

def subsetFamily (m r : ℕ) : Finset (Finset (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).powerset).filter (fun I => I.card = r)

def blockSum {m N : ℕ} (r : ℕ) (g : Index N → ℚ)
    (μ : Composition m N) : ℚ :=
  ∑ I ∈ subsetFamily m r, g (subsetIndex μ I)

def reflective (N : ℕ) (g : Index N → ℚ) : Prop :=
  ∀ t, g t = g (reflectIndex N t)

def sixFactorAnnihilator (N : ℕ) (f h k : Index N → ℚ) : Prop :=
  reflective N k ∧
    ∀ μ : Composition 6 N,
      blockSum 1 f μ + blockSum 2 h μ + blockSum 3 k μ = 0

def reflectiveSubmodule (N : ℕ) : Submodule ℚ (Index N → ℚ) where
  carrier := {g | reflective N g}
  zero_mem' := by
    intro t
    simp [reflective]
  add_mem' := by
    intro f g hf hg t
    simp only [Pi.add_apply]
    rw [hf t, hg t]
  smul_mem' := by
    intro c g hg t
    simp only [Pi.smul_apply]
    rw [hg t]

/-- The annihilator subspace of the compressed singleton/pair/triple rows. -/
def sixAnnihilatorSubmodule (N : ℕ) :
    Submodule ℚ ((Index N → ℚ) × (Index N → ℚ) × (Index N → ℚ)) where
  carrier := {x | sixFactorAnnihilator N x.1 x.2.1 x.2.2}
  zero_mem' := by
    constructor
    · intro t
      simp [reflective]
    · intro μ
      simp [blockSum]
  add_mem' := by
    intro x y hx hy
    constructor
    · intro t
      change x.2.2 t + y.2.2 t =
        x.2.2 (reflectIndex N t) + y.2.2 (reflectIndex N t)
      rw [hx.1 t, hy.1 t]
    · intro μ
      change (blockSum 1 (x.1 + y.1) μ +
        blockSum 2 (x.2.1 + y.2.1) μ +
          blockSum 3 (x.2.2 + y.2.2) μ = 0)
      have hx' := hx.2 μ
      have hy' := hy.2 μ
      simp only [blockSum, Pi.add_apply, Finset.sum_add_distrib] at *
      linear_combination hx' + hy'
  smul_mem' := by
    intro c x hx
    constructor
    · intro t
      change c * x.2.2 t = c * x.2.2 (reflectIndex N t)
      rw [hx.1 t]
    · intro μ
      change (blockSum 1 (c • x.1) μ +
        blockSum 2 (c • x.2.1) μ +
          blockSum 3 (c • x.2.2) μ = 0)
      have hx' := hx.2 μ
      simp only [blockSum, Pi.smul_apply, smul_eq_mul] at *
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      linear_combination c * hx'

/-- The three free coefficient blocks: singleton, pair, and folded
self-reciprocal triple coordinates. -/
abbrev SixCoordinate (N : ℕ) :=
  ((Fin (N + 1) ⊕ Fin (N + 1)) ⊕ Fin (N / 2 + 1))

def blockCount (ell N r : ℕ) (μ : Fin ell → Fin (N + 1))
    (t : Fin (N + 1)) : ℚ :=
  ∑ I : {I : Finset (Fin ell) // I.card = r},
    if Finset.sum I.1 (fun i => (μ i).val) = t.val then 1 else 0

def foldedTripleCount (N : ℕ) (μ : Fin 6 → Fin (N + 1))
    (t : Fin (N / 2 + 1)) : ℚ :=
  ∑ I : {I : Finset (Fin 6) // I.card = 3},
    if Finset.sum I.1 (fun i => (μ i).val) = t.val ∨
        Finset.sum I.1 (fun i => (μ i).val) = N - t.val then 1 else 0

def sixCompressedRow (N : ℕ) (μ : Fin 6 → Fin (N + 1)) :
    SixCoordinate N → ℚ :=
  fun z =>
    match z with
    | Sum.inl z' =>
        match z' with
        | Sum.inl t => blockCount 6 N 1 μ t
        | Sum.inr t => blockCount 6 N 2 μ t
    | Sum.inr t => foldedTripleCount N μ t

def sixCompressedRowSpan (N : ℕ) :
    Submodule ℚ (SixCoordinate N → ℚ) :=
  Submodule.span ℚ
    (Set.range (fun μ : Fin 6 → Fin (N + 1) =>
      if (∑ i, (μ i).val = N) then sixCompressedRow N μ else 0))

/-- Claim 25976: the nullity, free-coordinate dimension, row-span/D
identification, and rank formula all hold for `N ≥ 6`. -/
def claim25976 : Prop :=
  ∀ (N : ℕ), 6 ≤ N →
    Module.finrank ℚ (sixAnnihilatorSubmodule N) = 8 ∧
      Module.finrank ℚ (SixCoordinate N → ℚ) =
        2 * N + N / 2 + 3 ∧
      Module.finrank ℚ (sixCompressedRowSpan N) =
        Module.finrank ℚ
          (MathlibPlus.Algebra.Claim6218.monomialSpan 6 N) ∧
      Module.finrank ℚ (sixCompressedRowSpan N) +
          Module.finrank ℚ (sixAnnihilatorSubmodule N) =
        Module.finrank ℚ (SixCoordinate N → ℚ) ∧
      Module.finrank ℚ (SixCoordinate N → ℚ) -
          Module.finrank ℚ (sixAnnihilatorSubmodule N) =
        Module.finrank ℚ (sixCompressedRowSpan N) ∧
      Module.finrank ℚ (sixCompressedRowSpan N) =
        2 * N + N / 2 - 5

end

end MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976
