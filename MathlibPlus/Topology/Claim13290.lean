import Mathlib

namespace MathlibPlus.Topology.Claim13290

open Filter

/-- The exact endpoint witness from O-0292: the sequence `1 + 1/n` is
closed after restricting to `(1,∞)`, but its ambient infimum is `1`. -/
theorem relativeClosedness_no_positive_gap_claim13290 :
    let g : ℕ → ℝ := fun n => 1 + 1 / ((n + 1 : ℕ) : ℝ)
    let f : ℕ → Set.Ioi (1 : ℝ) := fun n =>
      ⟨g n, by
        dsimp [g]
        have hpos : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
        exact lt_add_of_pos_right 1 hpos⟩
    IsClosed (Set.range f) ∧ sInf (Set.range g) = 1 := by
  dsimp
  let g : ℕ → ℝ := fun n => 1 + 1 / ((n + 1 : ℕ) : ℝ)
  let f : ℕ → Set.Ioi (1 : ℝ) := fun n =>
    ⟨g n, by
      dsimp [g]
      have hpos : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
      exact lt_add_of_pos_right 1 hpos⟩
  have hshift : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    simpa [Nat.cast_add] using h
  have hinv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hshift
    simpa [one_div, Function.comp_def] using h
  have hg : Tendsto g atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hinv
    simpa [g] using h
  have hclosed : IsClosed (Set.range f) := by
    apply isClosed_range_of_not_tendsto
    intro l φ hφ hlim
    have hcomp : Tendsto (g ∘ φ) atTop (nhds 1) := hg.comp hφ.tendsto_atTop
    have hcomp' : Tendsto (g ∘ φ) atTop (nhds (l : ℝ)) := by
      have h := (continuous_subtype_val.tendsto l).comp hlim
      simpa [f, Function.comp_def] using h
    have heq : (1 : ℝ) = (l : ℝ) := tendsto_nhds_unique hcomp hcomp'
    have hl : (1 : ℝ) < (l : ℝ) := l.property
    linarith
  constructor
  · exact hclosed
  · have hne : (Set.range g).Nonempty := Set.range_nonempty _
    have hbdd : BddBelow (Set.range g) := by
      refine ⟨1, ?_⟩
      rintro x ⟨n, rfl⟩
      dsimp [g]
      have hpos : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hglb : IsGLB (Set.range g) 1 := by
      refine ⟨?_, ?_⟩
      · rintro x ⟨n, rfl⟩
        dsimp [g]
        have hpos : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
        linarith
      · intro b hb
        apply ge_of_tendsto hg
        exact Filter.Eventually.of_forall (fun n =>
          hb (Set.mem_range.2 ⟨n, rfl⟩))
    exact hglb.csInf_eq hne

end MathlibPlus.Topology.Claim13290
