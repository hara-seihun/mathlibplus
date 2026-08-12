import Mathlib

/-!
# Nonzero translation periods in `𝔽₁₃`

A subset of the additive group of `ZMod 13` that is invariant under a nonzero
translation is the whole field.  The first theorem is the exact period
implication; the second packages the nonempty-proper support consequence.
-/

namespace MathlibPlus.Algebra.Period13

/-- A nonempty subset of `𝔽₁₃` with a nonzero additive period is the whole
field. -/
theorem nonzeroPeriodForcesUniv
    (B : Set (ZMod 13)) (hB : B.Nonempty) (c : ZMod 13) (hc : c ≠ 0)
    (hperiod : ∀ x, x ∈ B ↔ x + c ∈ B) : B = Set.univ := by
  let P : AddSubgroup (ZMod 13) :=
    { carrier := {u | ∀ x, x ∈ B ↔ x + u ∈ B}
      zero_mem' := by
        intro x
        simp
      add_mem' := by
        intro u v hu hv x
        simpa [add_assoc] using (hu x).trans (hv (x + u))
      neg_mem' := by
        intro u hu x
        have h := hu (x + -u)
        simpa [sub_eq_add_neg, add_assoc] using h.symm }
  letI : Fact (Nat.card (ZMod 13)).Prime := ⟨by
    simpa [Nat.card_zmod] using (show Nat.Prime 13 by norm_num)⟩
  have hcP : c ∈ P := hperiod
  have hPne : P ≠ ⊥ := by
    intro hP
    have : c ∈ (⊥ : AddSubgroup (ZMod 13)) := hP ▸ hcP
    exact hc (by simpa using this)
  have hP : P = ⊤ := by
    rcases P.eq_bot_or_eq_top_of_prime_card with h | h
    · exact False.elim (hPne h)
    · exact h
  rcases hB with ⟨b, hb⟩
  ext x
  simp only [Set.mem_univ]
  have hu : x - b ∈ P := by
    rw [hP]
    trivial
  have hx : b + (x - b) ∈ B := (hu b).mp hb
  have hbx : b + (x - b) = x := by abel
  simpa [hbx] using hx

/-- Every nonempty proper support in `𝔽₁₃` has trivial additive period
subgroup. -/
theorem nonemptyProperHasNoNonzeroPeriod
    (B : Set (ZMod 13)) (hB : B.Nonempty) (hproper : B ≠ Set.univ) :
    ∀ c : ZMod 13, c ≠ 0 → ¬ (∀ x, x ∈ B ↔ x + c ∈ B) := by
  intro c hc hperiod
  exact hproper (nonzeroPeriodForcesUniv B hB c hc hperiod)

end MathlibPlus.Algebra.Period13
