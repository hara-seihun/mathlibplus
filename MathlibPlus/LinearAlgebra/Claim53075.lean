import Mathlib

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra

/-- For the zero-sum module on `A ^ B`, every assignment on at most two
coordinates extends to a zero-sum function.  The source parameters are made
explicit: `A = F_p^a`, `B = F_p^b`, with odd `p`, `a ≥ 1`, and `b ≥ 2`. -/
theorem zeroSumRestriction_surjective_claim53075
    (p a b : ℕ) [Fact (Nat.Prime p)] (hp : 2 < p)
    (ha : 1 ≤ a) (hb : 2 ≤ b)
    (I : Finset (Fin b → ZMod p)) (hI : I.card ≤ 2) :
    Function.Surjective
      (fun f : {f : (Fin b → ZMod p) → (Fin a → ZMod p) //
          ∑ x, f x = 0} =>
        fun i : I => f.1 i.1) := by
  have hcardB : Fintype.card (Fin b → ZMod p) = p ^ b := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hB : 2 < Fintype.card (Fin b → ZMod p) := by
    rw [hcardB]
    have hp3 : 3 ≤ p := by omega
    have hp2 : 3 ≤ p ^ 2 := by nlinarith
    have hpow : p ^ 2 ≤ p ^ b := Nat.pow_le_pow_right (by omega) hb
    omega
  have hnot : ¬(Finset.univ : Finset (Fin b → ZMod p)) ⊆ I := by
    intro h
    have hc : Fintype.card (Fin b → ZMod p) ≤ I.card := by
      simpa only [Finset.card_univ] using Finset.card_le_card h
    omega
  obtain ⟨b₀, hb₀univ, hb₀I⟩ := Finset.not_subset.mp hnot
  intro w
  let c : (Fin a → ZMod p) := -∑ i : I, w i
  let f : (Fin b → ZMod p) → (Fin a → ZMod p) := fun b' =>
    if hb' : b' ∈ I then w ⟨b', hb'⟩ else if b' = b₀ then c else 0
  have hfI : ∑ b' ∈ I, f b' = ∑ i : I, w i := by
    classical
    rw [Finset.sum_subtype I (fun _ => Iff.rfl)]
    apply Fintype.sum_congr
    intro i
    simp [f, i.property]
  have hfsupport : ∀ b' ∈ (Finset.univ : Finset (Fin b → ZMod p)),
      b' ∉ insert b₀ I → f b' = 0 := by
    intro b' _ hb'
    have hb'I : b' ∉ I := by
      intro hbi
      exact hb' (Finset.mem_insert_of_mem hbi)
    have hbb₀ : b' ≠ b₀ := by
      intro h
      exact hb' (by simp [h])
    simp [f, hb'I, hbb₀]
  have hsum_support :
      (∑ b' ∈ insert b₀ I, f b') = ∑ b' : (Fin b → ZMod p), f b' := by
    exact Finset.sum_subset (Finset.subset_univ _) hfsupport
  have hsum_insert :
      ∑ b' ∈ insert b₀ I, f b' = c + ∑ b' ∈ I, f b' := by
    rw [Finset.sum_insert]
    · simp [f, hb₀I]
    · exact hb₀I
  have hfzero : ∑ b' : (Fin b → ZMod p), f b' = 0 := by
    rw [← hsum_support, hsum_insert, hfI]
    simp [c]
  refine ⟨⟨f, hfzero⟩, ?_⟩
  funext i
  simp [f, i.property]

end MathlibPlus.LinearAlgebra
