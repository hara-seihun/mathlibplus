import Mathlib.Tactic

namespace MathlibPlus.GroupTheory

/-!
Claim 28514 is the local binary block-kernel lemma used by the larger
regular-subgroup result.  `Bool` gives an explicit two-point model of `C₂`:
`true` is the nontrivial swap and `false` is the identity on a block.
-/

/-- In a union of two-point blocks, the all-coordinate swap is the unique
fixed-point-free element of the binary block kernel. -/
theorem uniqueFixedPointFreeBinaryBlockElement_claim28514 (m : ℕ) :
    let act : (Fin m → Bool) → (Fin m × Bool) → (Fin m × Bool) :=
      fun g x => (x.1, if g x.1 then !x.2 else x.2)
    let fixedPointFree : (Fin m → Bool) → Prop :=
      fun g => ∀ x, act g x ≠ x
    (∀ g, fixedPointFree g ↔ ∀ i, g i = true) ∧
      (∀ g h, fixedPointFree g → fixedPointFree h → g = h) := by
  dsimp
  have hiff :
      ∀ g : Fin m → Bool,
        (∀ x : Fin m × Bool,
          (x.1, if g x.1 then !x.2 else x.2) ≠ x) ↔
          ∀ i, g i = true := by
    intro g
    constructor
    · intro h i
      by_contra hi
      have hfalse : g i = false := by
        cases hgi : g i <;> simp_all
      have hfix := h (i, false)
      apply hfix
      simp [hfalse]
    · intro hall x
      rcases x with ⟨i, b⟩
      have hi : g i = true := hall i
      simp only [hi, ↓reduceIte]
      cases b <;> simp
  constructor
  · exact hiff
  · intro g h hg hh
    have hgall := (hiff g).mp hg
    have hhall := (hiff h).mp hh
    funext i
    rw [hgall i, hhall i]

end MathlibPlus.GroupTheory
