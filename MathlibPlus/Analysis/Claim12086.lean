import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim12086

/-!
The source calls the adjacent log-concavity certificate `PF₂`; no local PF₂
predicate is supplied, so the exact coefficient nonnegativity, no-internal-zero
condition, and all adjacent 2-by-2 log-concavity inequalities are stated
explicitly below.
-/

/-- The scale-free quadratic family has the displayed PF₂ certificate and a
vanishing normalized derivative ratio as the scale tends to zero. -/
theorem scaleFreePF2CounterexampleFamily_claim12086 :
    (∀ t : ℝ, 0 < t →
      let F : ℝ → ℝ := fun z => 1 + (t / 2) * z + (t ^ 2 / 4) * z ^ 2
      let a : ℕ → ℝ := fun n =>
        if n = 0 then 1 else
        if n = 1 then t / 2 else
        if n = 2 then t ^ 2 / 4 else 0
      (∀ n, 0 ≤ a n) ∧
        (a 0 ≠ 0 ∧ a 1 ≠ 0 ∧ a 2 ≠ 0 ∧
          (∀ n, 3 ≤ n → a n = 0)) ∧
        (∀ n, a (n + 1) ^ 2 ≥ a n * a (n + 2)) ∧
        (a 1 ^ 2 = a 0 * a 2 ∧ a 2 ^ 2 ≥ a 1 * a 3) ∧
        (∀ z, F z = a 0 + a 1 * z + a 2 * z ^ 2) ∧
        ((1 / 4 : ℝ) * deriv F 0 / F 0 = t / 8)) ∧
    Filter.Tendsto (fun t : ℝ => t / 8)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  constructor
  · intro t ht
    dsimp
    constructor
    · intro n
      by_cases hn0 : n = 0
      · subst hn0
        norm_num
      by_cases hn1 : n = 1
      · subst hn1
        positivity
      by_cases hn2 : n = 2
      · subst hn2
        positivity
      simp [hn0, hn1, hn2]
    constructor
    · constructor
      · norm_num
      constructor
      · have : 0 < t / 2 := by positivity
        exact ne_of_gt this
      constructor
      · have : 0 < t ^ 2 / 4 := by positivity
        exact ne_of_gt this
      · intro n hn
        have hn0 : n ≠ 0 := by omega
        have hn1 : n ≠ 1 := by omega
        have hn2 : n ≠ 2 := by omega
        simp [hn0, hn1, hn2]
    constructor
    · intro n
      by_cases hn0 : n = 0
      · subst hn0
        norm_num
        nlinarith
      by_cases hn1 : n = 1
      · subst hn1
        norm_num
        positivity
      by_cases hn2 : n = 2
      · subst hn2
        norm_num
      simp [hn0, hn1, hn2]
    constructor
    · constructor
      · ring
      · norm_num
        positivity
    constructor
    · intro z
      simp
    · have hderiv :
          deriv (fun z : ℝ => 1 + (t / 2) * z + (t ^ 2 / 4) * z ^ 2) 0 = t / 2 := by
        have h := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
          ((hasDerivAt_const (x := (0 : ℝ)) (c := (t / 2 : ℝ))).mul
            (hasDerivAt_id (0 : ℝ)))
        have h := h.add
          ((hasDerivAt_const (x := (0 : ℝ)) (c := (t ^ 2 / 4 : ℝ))).mul
            ((hasDerivAt_id (0 : ℝ)).pow 2))
        have hfun :
            ((fun x : ℝ => 1) + (fun _ : ℝ => t / 2) * id) +
                (fun _ : ℝ => t ^ 2 / 4) * id ^ 2 =
              (fun z : ℝ => 1 + (t / 2) * z + (t ^ 2 / 4) * z ^ 2) := by
          funext z
          simp [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
        rw [hfun] at h
        simpa using h.deriv
      rw [hderiv]
      norm_num
      ring
  · have hid :
        Filter.Tendsto id (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
      Filter.tendsto_id.mono_left inf_le_left
    simpa using hid.div_const (8 : ℝ)

end MathlibPlus.Analysis.Claim12086
