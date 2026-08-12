import Mathlib

namespace MathlibPlus.Combinatorics.Claim49344

/-!
# Residual mass and common deck mass

Formalization of the algebraic core of admitted claim 49344 (packet R-3724).
A finite deck is represented by a natural-valued function on `Fin n`; equal
leaf count is the equal-total-mass hypothesis.  The source's tree/card-deck
constructors are not defined in the pinned environment, so this theorem keeps
the exact residual decomposition and its overlap/disjoint-support consequences
at the deck-vector level rather than silently inventing tree definitions.
-/

/-- Equal total deck mass decomposes into common mass and residual mass; the
residual is strictly smaller exactly when the two decks share a positive card
coordinate, and equality is exactly disjoint support. -/
theorem residualMassDecomposition {n : ℕ} (p q : Fin n → ℕ)
    (hL : (∑ i, p i) = ∑ i, q i) :
    let z : Fin n → ℕ := fun i => min (p i) (q i)
    let vp : Fin n → ℕ := fun i => p i - z i
    let vm : Fin n → ℕ := fun i => q i - z i
    let L : ℕ := ∑ i, p i
    let M : ℕ := ∑ i, vp i
    (L = M + ∑ i, z i) ∧
      (M = ∑ i, vm i) ∧
      (M < L ↔ ∑ i, z i ≠ 0) ∧
      ((∑ i, z i ≠ 0) ↔ ∃ i, 0 < p i ∧ 0 < q i) ∧
      (M = L ↔ ∀ i, p i = 0 ∨ q i = 0) := by
  dsimp
  let z : Fin n → ℕ := fun i => min (p i) (q i)
  let vp : Fin n → ℕ := fun i => p i - z i
  let vm : Fin n → ℕ := fun i => q i - z i
  let Z : ℕ := ∑ i, z i
  let M : ℕ := ∑ i, vp i
  let Mm : ℕ := ∑ i, vm i
  have hp : M + Z = ∑ i, p i := by
    dsimp [M, Z, vp, z]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.sub_add_cancel (min_le_left _ _)
  have hq : Mm + Z = ∑ i, q i := by
    dsimp [Mm, Z, vm, z]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.sub_add_cancel (min_le_right _ _)
  have hM : M = Mm := by
    omega
  have hdecomp : (∑ i, p i) = M + Z := hp.symm
  have hMlt : M < ∑ i, p i ↔ Z ≠ 0 := by
    constructor
    · intro hlt hz
      rw [hdecomp, hz, Nat.add_zero] at hlt
      exact (Nat.lt_irrefl _ hlt)
    · intro hz
      rw [hdecomp]
      exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hz)
  have hZ : Z ≠ 0 ↔ ∃ i, 0 < p i ∧ 0 < q i := by
    have hzero : Z = 0 ↔ ∀ i, z i = 0 := by
      dsimp [Z]
      simpa using
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset (Fin n)))
          (f := z) (by intro i hi; exact Nat.zero_le (z i)))
    have hne : Z ≠ 0 ↔ ¬ ∀ i, z i = 0 := by
      exact not_congr hzero
    rw [hne]
    constructor
    · intro hz
      push_neg at hz
      obtain ⟨i, hi⟩ := hz
      refine ⟨i, ?_, ?_⟩
      · have : p i ≠ 0 := by
          intro hp
          apply hi
          dsimp [z]
          simp [hp]
        exact Nat.pos_of_ne_zero this
      · have : q i ≠ 0 := by
          intro hq
          apply hi
          dsimp [z]
          simp [hq]
        exact Nat.pos_of_ne_zero this
    · rintro ⟨i, hip, hiq⟩ hz
      exact (by
        have hzi : z i ≠ 0 := by
          dsimp [z]
          simp [hip.ne', hiq.ne']
        exact hzi (hz i))
  have hM_eq : M = ∑ i, p i ↔ Z = 0 := by
    rw [hdecomp]
    constructor
    · intro h
      omega
    · intro h
      simp [h]
  have hdisjoint : M = ∑ i, p i ↔ ∀ i, p i = 0 ∨ q i = 0 := by
    rw [hM_eq]
    have hzero : Z = 0 ↔ ∀ i, z i = 0 := by
      dsimp [Z]
      simpa using
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset (Fin n)))
          (f := z) (by intro i hi; exact Nat.zero_le (z i)))
    rw [hzero]
    constructor
    · intro hz i
      have := hz i
      dsimp [z] at this
      simpa [min_eq_zero] using this
    · intro h i
      dsimp [z]
      simp [h i]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [M, Z, vp, z] using hdecomp
  · simpa [M, Mm, vm, z, hM]
  · simpa [M, Z, vp, z] using hMlt
  · simpa [Z, z] using hZ
  · simpa [M] using hdisjoint

end MathlibPlus.Combinatorics.Claim49344
