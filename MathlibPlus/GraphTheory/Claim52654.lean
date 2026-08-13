import Mathlib

namespace MathlibPlus.GraphTheory.Claim52654

/--
Claim 52654.  A finite directed path is represented by its vertex sequence
`v 0, ..., v N`; the two edge potentials are the corresponding successive
vertex differences.  Thus this statement quantifies over every such path,
without adding graph hypotheses not present in the source claim.
-/
theorem scalarAndActivityPotentialsTelescope
    {V V₀ : Type*} [AddCommGroup V₀]
    (Xi : V → V₀) (Phi : V → ℤ) (v : ℕ → V) (N : ℕ)
    (hXi : Xi (v 0) = Xi (v N))
    (hPhi : Phi (v 0) - Phi (v N) ≠ 0) :
    (∑ i ∈ Finset.range N, (Xi (v i) - Xi (v (i + 1)))) = 0 ∧
      (∑ i ∈ Finset.range N, (Phi (v i) - Phi (v (i + 1)))) =
        Phi (v 0) - Phi (v N) ∧
      Phi (v 0) - Phi (v N) ≠ 0 := by
  have htel : ∀ (f : ℕ → V₀),
      (∑ i ∈ Finset.range N, (f i - f (i + 1))) = f 0 - f N := by
    intro f
    calc
      (∑ i ∈ Finset.range N, (f i - f (i + 1))) =
          ∑ i ∈ Finset.range N, -(f (i + 1) - f i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simpa only [Nat.one_add] using
              (neg_sub (f (i + 1)) (f i)).symm
      _ = -(∑ i ∈ Finset.range N, (f (i + 1) - f i)) := by
            rw [Finset.sum_neg_distrib]
      _ = -(f N - f 0) := by rw [Finset.sum_range_sub]
      _ = f 0 - f N := by exact neg_sub _ _
  have hXiSum := htel (fun i => Xi (v i))
  have hXi' : (∑ i ∈ Finset.range N, (Xi (v i) - Xi (v (i + 1)))) =
      Xi (v 0) - Xi (v N) := hXiSum
  have hXiZero : (∑ i ∈ Finset.range N, (Xi (v i) - Xi (v (i + 1)))) = 0 := by
    rw [hXi', hXi, sub_self]
  have htelInt : ∀ (f : ℕ → ℤ),
      (∑ i ∈ Finset.range N, (f i - f (i + 1))) = f 0 - f N := by
    intro f
    calc
      (∑ i ∈ Finset.range N, (f i - f (i + 1))) =
          ∑ i ∈ Finset.range N, -(f (i + 1) - f i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simpa only [Nat.one_add] using
              (neg_sub (f (i + 1)) (f i)).symm
      _ = -(∑ i ∈ Finset.range N, (f (i + 1) - f i)) := by
            rw [Finset.sum_neg_distrib]
      _ = -(f N - f 0) := by rw [Finset.sum_range_sub]
      _ = f 0 - f N := by exact neg_sub _ _
  have hPhiSum' := htelInt (fun i => Phi (v i))
  exact ⟨hXiZero, hPhiSum', hPhi⟩

end MathlibPlus.GraphTheory.Claim52654
