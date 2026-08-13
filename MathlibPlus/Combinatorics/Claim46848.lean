import Mathlib

namespace MathlibPlus.Combinatorics

/-- In any finite probability mass, one of `p` fibers carries at least the
average mass.  This is the abstract residue-fiber pigeonhole core of claim
46848; the CRT progression and prime hypotheses are not needed for this step. -/
theorem claim46848_residue_fiber_pigeonhole
    {α : Type} [Fintype α] (p : ℕ) (hp : 0 < p) (μ : α → ℝ)
    (_hμ_nonneg : ∀ x, 0 ≤ μ x) (hμ : ∑ x, μ x = 1)
    (r : α → Fin p) :
    ∃ y : Fin p, (1 : ℝ) / p ≤ ∑ x with r x = y, μ x := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have havg : Fintype.card (Fin p) • ((1 : ℝ) / p) ≤ ∑ x, μ x := by
    rw [Fintype.card_fin, nsmul_eq_mul, hμ]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
    exact le_rfl
  obtain ⟨y, hy⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum r havg
  exact ⟨y, hy⟩

end MathlibPlus.Combinatorics
