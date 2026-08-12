import Mathlib

namespace MathlibPlus.Algebra.Claim28034

/-!
The isolated claim does not state its scalar domain.  The companion plane
statement places these coordinates in `F₃²`, so the formalization below uses
`ZMod 3`; the two basis vectors are represented by the displayed coordinate
vectors.
-/

/-- The displayed polar-span expression expands coordinatewise. -/
theorem polarSpan_identity (i j : ZMod 3) :
    (2 * (i - 1)) • ![2 * i, 2 * j, 0] +
        (2 * j) • ![0, 2 * i, 2 * j] =
      ![4 * i * (i - 1), 4 * j * (2 * i - 1), 4 * j ^ 2] := by
  funext n
  fin_cases n <;> simp <;> ring

/-- The zero locus of the polar-span expression has exactly two points. -/
theorem polarSpan_zero_locus :
    ∀ i j : ZMod 3,
      ((2 * (i - 1)) • ![2 * i, 2 * j, 0] +
          (2 * j) • ![0, 2 * i, 2 * j] = 0) ↔
        ((i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0)) := by
  intro i j
  have h4ne : (4 : ZMod 3) ≠ 0 := by
    intro h4
    have hdiv : (3 : ℤ) ∣ 4 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd 4 3).mp h4
    norm_num at hdiv
  constructor
  · intro h
    have h₂ : j ^ 2 = 0 := by
      have h := congrFun h 2
      change (2 * (i - 1)) * 0 + (2 * j) * (2 * j) = 0 at h
      ring_nf at h
      rcases mul_eq_zero.mp h with hj | h4
      · exact hj
      · exact (h4ne h4).elim
    have hj : j = 0 := (sq_eq_zero_iff).mp h₂
    have h₀ : i * (i - 1) = 0 := by
      have h := congrFun h 0
      change (2 * (i - 1)) * (2 * i) + (2 * j) * 0 = 0 at h
      ring_nf at h
      have h' : (i * (i - 1)) * 4 = 0 := by
        calc
          (i * (i - 1)) * 4 = -(i * 4) + i ^ 2 * 4 := by ring
          _ = 0 := h
      rcases mul_eq_zero.mp h' with hᵢ | h4
      · exact hᵢ
      · exact (h4ne h4).elim
    rcases mul_eq_zero.mp h₀ with hi | hi
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr ⟨sub_eq_zero.mp hi, hj⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · ext n
      fin_cases n <;> simp
    · ext n
      fin_cases n <;> simp

end MathlibPlus.Algebra.Claim28034
