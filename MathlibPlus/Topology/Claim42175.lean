import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.Topology

/--
The explicit relative-topology witness from admitted claim 42175.  The index
`n + 1` is the source's positive-natural index, so the displayed range is
`{1 + 1/n | n ∈ ℕ, n > 0}`.
-/
theorem relativelyClosedApproachesEndpoint_claim42175 :
    let X := {x : ℝ // 1 < x}
    let f : ℕ → X := fun n =>
      ⟨1 + 1 / ((n : ℝ) + 1), by
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hdiv : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
        linarith⟩
    IsClosed (Set.range f) ∧
      sInf ((fun x : X => (x : ℝ)) '' Set.range f) = 1 := by
  dsimp
  let X := {x : ℝ // 1 < x}
  let f : ℕ → X := fun n =>
    ⟨1 + 1 / ((n : ℝ) + 1), by
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hdiv : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
      linarith⟩
  have hfclosed : IsClosed (Set.range f) := by
    apply isClosed_range_of_not_tendsto
    intro l φ hφ hlim
    have hlim_val :
        Tendsto (fun n : ℕ => (f (φ n) : ℝ)) atTop (𝓝 (l : ℝ)) := by
      simpa [Function.comp_def] using
        ((continuous_subtype_val.tendsto l).comp hlim)
    have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1))
        atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφtop
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((φ n : ℝ) + 1))
        atTop (𝓝 1) := by
      have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      simpa using hconst.add hzero
    have hone' :
        Tendsto (fun n : ℕ => (f (φ n) : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa [f, Function.comp_def] using hone
    have h_eq : (l : ℝ) = 1 := tendsto_nhds_unique hlim_val hone'
    have hl : (1 : ℝ) < (l : ℝ) := l.property
    linarith
  constructor
  · exact hfclosed
  · rw [← Set.range_comp]
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt (Set.range_nonempty _)
    · rintro _ ⟨n, rfl⟩
      dsimp [f]
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hdiv : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
      linarith
    · intro w hw
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hw)
      refine ⟨(fun x : X => (x : ℝ)) (f n), ⟨n, rfl⟩, ?_⟩
      dsimp [f]
      linarith

end MathlibPlus.Topology
