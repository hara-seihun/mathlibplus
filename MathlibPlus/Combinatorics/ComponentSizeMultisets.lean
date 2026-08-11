import Mathlib

/-!
# Component-size multiset rigidity

Formalization of admitted claim 23515.  The notation `{d^(q-1), d-1}` is
represented literally as `q - 1` copies of `d` together with one copy of `d - 1`.
-/

namespace MathlibPlus.Combinatorics.ComponentSizeMultisets

/-- Equality of the two component-size multisets determines both parameters. -/
theorem equality_injective
    (p c q d : ℕ) (hp : 2 ≤ p) (hc : 2 ≤ c) (hq : 2 ≤ q) (hd : 2 ≤ d)
    (h : Multiset.replicate (q - 1) d + {d - 1} =
      Multiset.replicate (p - 1) c + {c - 1}) :
    d = c ∧ q = p := by
  have hd_mem : d ∈ Multiset.replicate (q - 1) d + {d - 1} := by
    apply Multiset.mem_add.mpr
    left
    exact Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
  have hc_mem : c ∈ Multiset.replicate (p - 1) c + {c - 1} := by
    apply Multiset.mem_add.mpr
    left
    exact Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
  have hd_right : d ∈ Multiset.replicate (p - 1) c + {c - 1} := by
    rw [← h]
    exact hd_mem
  have hc_left : c ∈ Multiset.replicate (q - 1) d + {d - 1} := by
    rw [h]
    exact hc_mem
  have hd_cases : d = c ∨ d = c - 1 := by
    rw [Multiset.mem_add] at hd_right
    rcases hd_right with hd_rep | hd_last
    · exact Or.inl (Multiset.mem_replicate.mp hd_rep).2
    · exact Or.inr (by simpa using hd_last)
  have hc_cases : c = d ∨ c = d - 1 := by
    rw [Multiset.mem_add] at hc_left
    rcases hc_left with hc_rep | hc_last
    · exact Or.inl (Multiset.mem_replicate.mp hc_rep).2
    · exact Or.inr (by simpa using hc_last)
  have hdc : d = c := by omega
  have hcard := congrArg Multiset.card h
  have hqcard : (Multiset.replicate (q - 1) d + {d - 1}).card = q := by
    simp
    omega
  have hpcard : (Multiset.replicate (p - 1) c + {c - 1}).card = p := by
    simp
    omega
  exact ⟨hdc, by omega⟩

end MathlibPlus.Combinatorics.ComponentSizeMultisets
