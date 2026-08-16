import Mathlib

namespace MathlibPlus.Analysis

section

variable {X R : Type*} [CommRing R]

/-- The finite polarized Turán form from claim 4408, for a fixed parameter `x`.
The coefficient sequence `p x` carries all dependence on `x`; no conjugation is
part of this bilinear form. -/
def polarizedTuranForm (p : X → ℕ → R) (x : X) (N : ℕ)
    (u v : ℕ → R) : R :=
  ∑ n ∈ Finset.range N,
    p x n * (u n * v (n + 2) - u (n + 1) * v (n + 1))

@[simp] theorem polarizedTuranForm_zero (p : X → ℕ → R) (x : X)
    (u v : ℕ → R) :
    polarizedTuranForm p x 0 u v = 0 := by
  simp [polarizedTuranForm]

theorem polarizedTuranForm_add_left (p : X → ℕ → R) (x : X) (N : ℕ)
    (u u' v : ℕ → R) :
    polarizedTuranForm p x N (u + u') v =
      polarizedTuranForm p x N u v + polarizedTuranForm p x N u' v := by
  simp only [polarizedTuranForm, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem polarizedTuranForm_add_right (p : X → ℕ → R) (x : X) (N : ℕ)
    (u v v' : ℕ → R) :
    polarizedTuranForm p x N u (v + v') =
      polarizedTuranForm p x N u v + polarizedTuranForm p x N u v' := by
  simp only [polarizedTuranForm, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The exact zero-length and separate additivity properties of the form. -/
theorem polarizedTuranForm_properties_claim4408 (p : X → ℕ → R) :
    (∀ (x : X) (u v : ℕ → R), polarizedTuranForm p x 0 u v = 0) ∧
      (∀ (x : X) (N : ℕ) (u u' v : ℕ → R),
        polarizedTuranForm p x N (u + u') v =
          polarizedTuranForm p x N u v + polarizedTuranForm p x N u' v) ∧
      (∀ (x : X) (N : ℕ) (u v v' : ℕ → R),
        polarizedTuranForm p x N u (v + v') =
          polarizedTuranForm p x N u v + polarizedTuranForm p x N u v') := by
  exact ⟨polarizedTuranForm_zero p, polarizedTuranForm_add_left p,
    polarizedTuranForm_add_right p⟩

end
end MathlibPlus.Analysis
