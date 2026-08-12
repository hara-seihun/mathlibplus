import MathlibPlus.Basic

open Set Filter
open scoped Topology

namespace MathlibPlus.Topology.Claim13287

/-- The endpoint witness from claim 13287: the positive reciprocal sequence tends to
one, while one is a genuine accumulation point of its range but is not itself in
that range (nor in the open interval above one). -/
theorem endpoint_accumulation :
    let E : Set ℝ := {x | ∃ n : ℕ, 1 ≤ n ∧ x = 1 + 1 / (n : ℝ)}
    Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 1) ∧
      (1 : ℝ) ∈ closure E ∧
      (1 : ℝ) ∉ E ∧
      (1 : ℝ) ∉ Ioi 1 := by
  let E : Set ℝ := {x | ∃ n : ℕ, 1 ≤ n ∧ x = 1 + 1 / (n : ℝ)}
  change
    Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 1) ∧
      (1 : ℝ) ∈ closure E ∧
      (1 : ℝ) ∉ E ∧
      (1 : ℝ) ∉ Ioi 1
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa [one_div] using tendsto_const_nhds.add hinv
  have hshift :
      Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp
        ((tendsto_add_atTop_iff_nat 1).2 tendsto_id)
    have hshift0 :
        Tendsto (fun n : ℕ => (1 : ℝ) + ((n + 1 : ℕ) : ℝ)⁻¹) atTop
          (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hcast)
    simpa [one_div] using hshift0
  have hmem : ∀ n : ℕ, (1 : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) ∈ E := by
    intro n
    exact ⟨n + 1, Nat.le_add_left 1 n, rfl⟩
  have hclosure : (1 : ℝ) ∈ closure E :=
    mem_closure_of_tendsto hshift (Filter.Eventually.of_forall hmem)
  have hnot : (1 : ℝ) ∉ E := by
    rintro ⟨n, hn, hval⟩
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hpositive : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  exact ⟨hseq, hclosure, hnot, by simp⟩

end MathlibPlus.Topology.Claim13287
