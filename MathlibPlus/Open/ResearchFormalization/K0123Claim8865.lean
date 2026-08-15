import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.K0123

noncomputable def claim8865 : Prop :=
  let cauchyPrincipalValue : (ℝ → ℝ) → ℝ → ℝ → Prop := fun f z L =>
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ w in Set.Ioc (0 : ℝ) (z - ε), f w) +
          (∫ w in Set.Ioi (z + ε), f w))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds L)
  let b : ℝ := Real.pi / 2
  let rhoStar : ℝ → ℝ := fun z =>
    if 0 < z then
      if z < b then
        (z ^ 2)⁻¹ * (1 - Real.sqrt (1 - (z / b) ^ 2))
      else
        (z ^ 2)⁻¹
    else
      0
  let potential : ℝ → ℝ := fun z =>
    2 * ∫ w in Set.Ioi (0 : ℝ), Real.log |z ^ 2 - w ^ 2| * rhoStar w
  ∃ H : ℝ → ℝ,
    (∀ z : ℝ, 0 < z →
      cauchyPrincipalValue (fun w : ℝ => rhoStar w / (z ^ 2 - w ^ 2)) z (H z)) ∧
      (∀ z : ℝ, 0 < z → HasDerivAt potential (4 * z * H z) z) ∧
      (∃ c : ℝ, ∀ z : ℝ, z ∈ Set.Ioo (0 : ℝ) b → potential z = c) ∧
      StrictMonoOn potential (Set.Ioi b)

end MathlibPlus.Open.ResearchFormalization.K0123
