import Mathlib

namespace MathlibPlus.Analysis.Claim4412

/--
Claim 4412, formalized exactly on a dyadic block.  The two block hypotheses
are retained even though the four displayed algebraic consequences use only
`0 < T`.
-/
theorem twoThirdsDyadicCorrelation
    (T t s : ℝ) (hT : 0 < T)
    (_ht : T ≤ t ∧ t ≤ 2 * T) (_hs : T ≤ s ∧ s ≤ 2 * T) :
    let uT : ℝ → ℝ → ℝ :=
      fun x y => (x - y) / Real.rpow T (2 / 3 : ℝ)
    uT t s = -uT s t ∧
      uT t t = 0 ∧
      (uT t s = 0 ↔ t = s) ∧
      ∀ u : ℝ, t - s = u * Real.rpow T (2 / 3 : ℝ) → uT t s = u := by
  let r : ℝ := Real.rpow T (2 / 3 : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos hT _
  have hrne : r ≠ 0 := ne_of_gt hr
  dsimp
  constructor
  · ring
  constructor
  · ring
  constructor
  · constructor
    · intro h
      have hsub : t - s = 0 := by
        have h' := (div_eq_iff hrne).mp h
        simpa using h'
      exact sub_eq_zero.mp hsub
    · intro hts
      subst s
      ring
  · intro u hu
    exact (div_eq_iff hrne).mpr hu

end MathlibPlus.Analysis.Claim4412
