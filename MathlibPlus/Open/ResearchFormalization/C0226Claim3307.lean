import MathlibPlus.Open.ResearchFormalization.C0226Claims3302_3306_3308

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0226

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Batch

/-- Claim 3307: the gap-and-strip lower bound for the normalized half-line
Gram matrix, with the node count and the separation factor retained. -/
def half_line_gram_lower_bound_claim3307 : Prop :=
  ∀ (n : ℕ) (y t : Fin (n + 1) → ℝ)
    (Y d L : ℝ),
    0 < Y →
    0 < d →
    0 < L →
    (∀ j, 0 < y j ∧ y j ≤ Y) →
    (∀ j : Fin n,
      t (Fin.succ j) - t (Fin.castSucc j) ≥ d / L) →
      let s : Fin (n + 1) → ℂ :=
        fun j => halfPlaneParameter (y j) (t j)
      let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
        fun j k =>
          ((2 : ℂ) * Real.sqrt (y j * y k)) /
            (s j + star (s k))
      let a : ℝ := 2 * Y * L / d
      complexLeastEigenvalue K ≥
        (1 / ((n + 1 : ℕ) : ℝ)) * (separationSineRatio a) ^ 2

end
end MathlibPlus.Open.ResearchFormalization.C0226
