import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 19074: a finite head and a positive-threshold tail leave infinitely
many zero-height lattice points uncovered. -/
theorem finiteHeadHighIndexLatticeCover_claim19074
    (C : Finset (ℕ × ℕ)) (N : ℕ → ℕ)
    (hN : ∀ d, 0 < N d) :
    Set.Infinite
      (((C : Set (ℕ × ℕ)) ∪ {p | N p.1 ≤ p.2})ᶜ) := by
  let zeroRow : Set (ℕ × ℕ) := Set.range (fun d : ℕ => (d, 0))
  have hzero : zeroRow.Infinite := by
    apply Set.infinite_range_of_injective
    intro d₁ d₂ h
    exact congrArg Prod.fst h
  have hmiss : (zeroRow \ (C : Set (ℕ × ℕ))).Infinite :=
    hzero.sdiff C.finite_toSet
  apply hmiss.mono
  intro p hp
  rcases hp with ⟨⟨d, rfl⟩, hpC⟩
  change (d, 0) ∉ (C : Set (ℕ × ℕ)) ∪ {p | N p.1 ≤ p.2}
  intro hpUnion
  rcases hpUnion with hpC' | hpTail
  · exact hpC hpC'
  · exact (not_le_of_gt (hN d)) hpTail

/-- The high-index refinement in claim 19074: if the finite head has no first
coordinate above `D`, every point below the positive tail threshold at a larger
first coordinate is uncovered. -/
theorem finiteHeadHighIndexLatticeCover_belowTail_claim19074
    (C : Finset (ℕ × ℕ)) (N : ℕ → ℕ) (D : ℕ)
    (hC : ∀ p ∈ C, p.1 ≤ D) :
    {p : ℕ × ℕ | D < p.1 ∧ p.2 < N p.1} ⊆
      (((C : Set (ℕ × ℕ)) ∪ {p | N p.1 ≤ p.2})ᶜ) := by
  intro p hp
  rcases hp with ⟨hpD, hpN⟩
  change p ∉ (C : Set (ℕ × ℕ)) ∪ {p | N p.1 ≤ p.2}
  intro hpUnion
  rcases hpUnion with hpC | hpTail
  · have h := hC p hpC
    omega
  · change N p.1 ≤ p.2 at hpTail
    omega

end MathlibPlus.Combinatorics
