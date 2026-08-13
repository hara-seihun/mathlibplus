import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 8034.  The finite arithmetic progressions
`M - 1, M - 3, ..., 1 - M` and `N - 1, N - 3, ..., 1 - N` are disjoint when
`M` and `N` have opposite parity. -/
theorem oppositeParityGainGrids_disjoint_claim8034 :
    ∀ M N : ℕ, 0 < M → 0 < N → M % 2 ≠ N % 2 →
      Disjoint
        ((Finset.range M).image
          (fun i : ℕ => (M : ℤ) - 1 - 2 * (i : ℤ)))
        ((Finset.range N).image
          (fun j : ℕ => (N : ℤ) - 1 - 2 * (j : ℤ))) := by
  intro M N hM hN hpar
  rw [Finset.disjoint_left]
  intro z hzM hzN
  simp only [Finset.mem_image, Finset.mem_range] at hzM hzN
  rcases hzM with ⟨i, hi, hzi⟩
  rcases hzN with ⟨j, hj, hzj⟩
  have heq :
      (M : ℤ) - 1 - 2 * (i : ℤ) =
        (N : ℤ) - 1 - 2 * (j : ℤ) := hzi.trans hzj.symm
  omega

end MathlibPlus.Combinatorics
