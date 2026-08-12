import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim52019

/-!
Formalization of admitted claim 52019 (legacy packet R-4032).  The exact
fixed-level table and the three component savings are retained inside the
statement.  The source's minimum-decision-tree definition of `q` and the
deleted-coordinate maps are not supplied as Lean interfaces here; the displayed
exact savings table is therefore recorded directly, rather than replaced by a
silently chosen model.
-/

/-- The displayed fixed-level law has variance `4687/6241`, while its largest
component saving is `58/79`; hence the coefficient-one saving inequality fails. -/
theorem targetVarianceAndObstruction :
    let targetTable : Fin 8 → ℚ :=
      ![1, -1, 1, -1, 1, 5 / 79, -5 / 79, -1]
    let componentSavings : Fin 3 → ℚ :=
      ![42 / 79, 21 / 79, 58 / 79]
    let x : Fin 8 → ℚ := ![-1, -1, -1, -1, 1, 1, 1, 1]
    let y₁ : Fin 8 → ℚ := ![-1, -1, 1, 1, -1, -1, 1, 1]
    let y₂ : Fin 8 → ℚ := ![-1, 1, -1, 1, -1, 1, -1, 1]
    let t₁ : Fin 8 → ℚ := fun i => -y₂ i
    let t₂ : Fin 8 → ℚ := fun i => if x i = -1 then -y₂ i else -y₁ i
    let g : Fin 8 → ℚ := fun i => (37 * t₁ i + 42 * t₂ i) / 79
    let m : ℚ := (∑ i, g i) / 8
    g = targetTable ∧
      componentSavings 0 = 42 / 79 ∧
      componentSavings 1 = 21 / 79 ∧
      componentSavings 2 = 58 / 79 ∧
      m = 0 ∧
      (∑ i, (g i - m) ^ 2) / 8 = 4687 / 6241 ∧
      (58 : ℚ) / 79 = 4582 / 6241 ∧
      (∑ i, (g i - m) ^ 2) / 8 >
        max (max (componentSavings 0) (componentSavings 1))
          (componentSavings 2) ∧
      ¬ (∑ i, (g i - m) ^ 2) / 8 ≤
        max (max (componentSavings 0) (componentSavings 1))
          (componentSavings 2) := by
  native_decide

end MathlibPlus.Analysis.Claim52019
