import MathlibPlus.Basic

open unitInterval

namespace MathlibPlus.Topology

/-- Claim 12945: the time-t map of a continuous flow is homotopic to the
identity through the rescaled-time maps `u ↦ φ (u * t)`. -/
theorem claim12945_flowTimeMapHomotopy
    {X : Type*} [TopologicalSpace X]
    (φ : ℝ → X → X)
    (hcont : Continuous (fun p : ℝ × X => φ p.1 p.2))
    (hzero : ∀ x, φ 0 x = x)
    (hflow : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (t : ℝ) :
    ContinuousMap.Homotopic (ContinuousMap.id X)
      (⟨φ t, hcont.comp (continuous_const.prodMk continuous_id)⟩ :
        ContinuousMap X X) := by
  let f : ContinuousMap X X :=
    ⟨φ t, hcont.comp (continuous_const.prodMk continuous_id)⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id X) f :=
    { toContinuousMap :=
        { toFun := fun p : I × X => φ ((p.1 : ℝ) * t) p.2
          continuous_toFun := by
            have harg : Continuous (fun p : I × X => ((p.1 : ℝ) * t, p.2)) :=
              ((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
                continuous_snd
            exact hcont.comp harg }
      map_zero_left := by
        intro x
        simp [f, hzero]
      map_one_left := by
        intro x
        simp [f] }
  exact ⟨H⟩

end MathlibPlus.Topology
