import MathlibPlus.Basic

open Set Filter
open scoped Topology

namespace MathlibPlus.Topology.Claim12355

/-- A convergent sequence of counterexamples cannot approach a point lying in
an open region on which the predicate holds on the specified target set. -/
theorem accumulating_counterexample_interior
    {X Y : Type*} [TopologicalSpace Y]
    (x₀ : X) (x : ℕ → X) (D : X → Y) (U : Set Y) (Good : X → Prop)
    (hbad : ∀ n : ℕ, 1 ≤ n → ¬ Good (x n))
    (hgood : ∀ y : X, y ∈ ({x₀} ∪ range x) → D y ∈ U → Good y)
    (hlim : Tendsto (fun n => D (x n)) atTop (𝓝 (D x₀)))
    (hopen : IsOpen U) :
    D x₀ ∉ U := by
  intro hx₀
  have hU : U ∈ 𝓝 (D x₀) := hopen.mem_nhds hx₀
  have hev : ∀ᶠ n in atTop, D (x n) ∈ U := hlim.eventually hU
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hev)
  have hNm : 1 ≤ N + 1 := by omega
  have hU' : D (x (N + 1)) ∈ U := hN (N + 1) (by omega)
  have hgood' := hgood (x (N + 1)) (mem_union_right _ (mem_range_self _)) hU'
  exact hbad (N + 1) hNm hgood'

end MathlibPlus.Topology.Claim12355
