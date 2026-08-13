import Mathlib

namespace MathlibPlus.Analysis.Claim42822

/-- Finite telescoping form of the dyadic inversion in claim 42822. -/
theorem dyadic_telescoping_claim42822
    (A F : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hrec : ∀ y, 0 < y → F y = A y - A (2 * y)) (N : ℕ) :
    ∑ j ∈ Finset.range N, F ((2 : ℝ) ^ j * x) =
      A x - A ((2 : ℝ) ^ N * x) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, hrec _ (by positivity)]
      have hpow : (2 : ℝ) ^ (N + 1) * x =
          2 * ((2 : ℝ) ^ N * x) := by
        rw [pow_succ]
        ring
      rw [hpow]
      ring

/-- Infinite dyadic inversion, with the summability hypothesis required by
Lean's unconditional `tsum` for a possibly signed series. -/
theorem dyadic_inversion_claim42822
    (A F : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hrec : ∀ y, 0 < y → F y = A y - A (2 * y))
    (hsum : Summable (fun j : ℕ => F ((2 : ℝ) ^ j * x)))
    (hlim : Filter.Tendsto (fun N : ℕ => A ((2 : ℝ) ^ N * x))
      Filter.atTop (nhds 0)) :
    A x = ∑' j : ℕ, F ((2 : ℝ) ^ j * x) := by
  have hpartial : Filter.Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range N, F ((2 : ℝ) ^ j * x))
      Filter.atTop (nhds (A x)) := by
    have hsub : Filter.Tendsto
        (fun N : ℕ => A x - A ((2 : ℝ) ^ N * x))
        Filter.atTop (nhds (A x)) := by
      simpa using (tendsto_const_nhds.sub hlim)
    exact hsub.congr' (Filter.Eventually.of_forall fun N =>
      (dyadic_telescoping_claim42822 A F x hx hrec N).symm)
  have hsum_ax : HasSum (fun j : ℕ => F ((2 : ℝ) ^ j * x)) (A x) :=
    (hsum.hasSum_iff_tendsto_nat).2 hpartial
  exact hsum_ax.unique hsum.hasSum

end MathlibPlus.Analysis.Claim42822
