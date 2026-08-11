import MathlibPlus.Basic

open Filter
open scoped Topology

namespace MathlibPlus.Analysis.PeriodicLimit

/-- Claim 11526: a real-valued two-periodic function with limit `1` at `+∞`
is identically `1`. -/
theorem tendsto_periodic_two_eq_one {P : ℝ → ℝ}
    (hper : ∀ x : ℝ, P (x + 2) = P x)
    (hlim : Tendsto P atTop (𝓝 1)) :
    ∀ x : ℝ, P x = 1 := by
  intro x
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have hx : Tendsto (fun n : ℕ => x + 2 * (n : ℝ)) atTop atTop := by
    refine tendsto_atTop_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 htwo (b - x)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    linarith
  have hvalues : Tendsto (fun n : ℕ => P (x + 2 * (n : ℝ))) atTop (𝓝 1) :=
    hlim.comp hx
  have hconst : ∀ n : ℕ, P (x + 2 * (n : ℝ)) = P x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show x + 2 * ((n + 1 : ℕ) : ℝ) = (x + 2 * (n : ℝ)) + 2 by
        push_cast
        ring]
      rw [hper]
      exact ih
  have hconst' : Tendsto (fun _ : ℕ => P x) atTop (𝓝 1) := by
    simpa only [hconst] using hvalues
  exact tendsto_nhds_unique tendsto_const_nhds hconst'

end MathlibPlus.Analysis.PeriodicLimit
