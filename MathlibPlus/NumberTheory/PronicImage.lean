import Mathlib

namespace MathlibPlus.NumberTheory.PronicImage

private lemma pronic_strictMono : StrictMono (fun u : ℕ => u * (u + 1)) := by
  intro u v huv
  calc
    u * (u + 1) < v * (u + 1) := Nat.mul_lt_mul_of_pos_right huv (Nat.succ_pos u)
    _ ≤ v * (v + 1) := Nat.mul_le_mul_left v (Nat.succ_le_succ (Nat.le_of_lt huv))

/--
Claim 35342's explicit pronic-image substatement.  The source additionally
introduces `z = √(N / log N)` for the later sieve argument; that parameter is
not used by this base-image containment and cardinality assertion.
-/
theorem pronicImage_subset_card (X : ℕ) (_hX : 1 ≤ X) :
    let N := X * (X + 1) + 1
    let S := (Finset.Icc 0 X).image (fun u => u * (u + 1))
    S ⊆ Finset.Icc 0 (N - 1) ∧ S.card = X + 1 := by
  dsimp
  constructor
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
    have huX : u ≤ X := (Finset.mem_Icc.mp hu).2
    have hupper : u * (u + 1) ≤ X * (X + 1) := by
      exact Nat.mul_le_mul huX (Nat.succ_le_succ huX)
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.zero_le _
    · simpa [Nat.add_sub_cancel] using hupper
  · rw [Finset.card_image_iff.mpr pronic_strictMono.injective.injOn]
    have hIcc : Finset.Icc 0 X = Finset.range (X + 1) := by
      ext u
      simp [Finset.mem_Icc]
    rw [hIcc, Finset.card_range]

end MathlibPlus.NumberTheory.PronicImage
