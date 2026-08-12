import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace MathlibPlus.Algebra.Claim53590

/-!
Formalization of admitted claim 53590 (packet `R-4716.1`).  A finite support
`S` is represented by a nonempty finite type `ι`; `L` is a linear map from the
coordinate space `ι → ℚ`, and `scalarColumn L e` is its image of the `e`th
coordinate vector.  Thus `scalarSpan L` is the source's `W`.
-/

/-- The scalar column indexed by `e`. -/
noncomputable def scalarColumn {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V]
    (L : (ι → ℚ) →ₗ[ℚ] V) (e : ι) : V := by
  classical
  exact L (Pi.single e 1)

/-- The span of the scalar columns. -/
noncomputable def scalarSpan {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V]
    (L : (ι → ℚ) →ₗ[ℚ] V) : Submodule ℚ V := by
  classical
  exact Submodule.span ℚ (Set.range (scalarColumn L))

/-- The coordinate-map range is exactly the span of its scalar columns. -/
theorem range_eq_scalarSpan {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V]
    (L : (ι → ℚ) →ₗ[ℚ] V) :
    LinearMap.range L = scalarSpan L := by
  classical
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change L x ∈ Submodule.span ℚ (Set.range (scalarColumn L))
    have hexpand : (∑ e : ι, x e • Pi.single e 1) = x := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← hexpand]
    rw [map_sum]
    apply Submodule.sum_mem
    intro e he
    rw [map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨e, by simp [scalarColumn]⟩
  · intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro x ⟨e, rfl⟩
      exact ⟨Pi.single e 1, by simp [scalarColumn]⟩
    · exact ⟨0, by simp⟩
    · intro x z hx hz ihx ihz
      rcases ihx with ⟨x', hx'⟩
      rcases ihz with ⟨z', hz'⟩
      refine ⟨x' + z', ?_⟩
      simp [map_add, hx', hz']
    · intro a x hx ih
      rcases ih with ⟨x', hx'⟩
      refine ⟨a • x', ?_⟩
      simp [map_smul, hx']

/-- Positive circuit weights give the claimed span dimension and barycentric relation. -/
theorem positive_scalar_circuit_data {ι V : Type*} [Fintype ι] [Nonempty ι]
    [AddCommGroup V] [Module ℚ V]
    (L : (ι → ℚ) →ₗ[ℚ] V) (q : ι → ℚ)
    (hq : ∀ e, 0 < q e)
    (hker : LinearMap.ker L = Submodule.span ℚ ({q} : Set (ι → ℚ))) :
    Module.finrank ℚ (scalarSpan L) = Fintype.card ι - 1 ∧
      0 < ∑ e : ι, q e ∧
      (∑ e : ι, (q e / ∑ f : ι, q f) • scalarColumn L e) = 0 := by
  classical
  have hq0 : q ≠ 0 := by
    intro hzero
    have hi := hq (Classical.choice (inferInstance : Nonempty ι))
    rw [hzero] at hi
    exact (lt_irrefl 0) hi
  have hker_finrank : Module.finrank ℚ (LinearMap.ker L) = 1 := by
    rw [hker]
    exact finrank_span_singleton hq0
  have hdim := L.finrank_range_add_finrank_ker
  rw [hker_finrank, Module.finrank_pi] at hdim
  have hspan_dim : Module.finrank ℚ (scalarSpan L) = Fintype.card ι - 1 := by
    rw [← range_eq_scalarSpan L]
    omega
  have hsum_pos : 0 < ∑ e : ι, q e := by
    apply Finset.sum_pos' (fun e _ => le_of_lt (hq e))
    exact ⟨Classical.choice (inferInstance : Nonempty ι), by simp,
      hq (Classical.choice (inferInstance : Nonempty ι))⟩
  have hLq : L q = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact Submodule.subset_span (by simp)
  have hexpand : (∑ e : ι, q e • Pi.single e 1) = q := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hcolumns : (∑ e : ι, q e • scalarColumn L e) = 0 := by
    simp only [scalarColumn]
    calc
      (∑ e : ι, q e • L (Pi.single e 1)) =
          ∑ e : ι, L (q e • Pi.single e 1) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [map_smul]
      _ = L (∑ e : ι, q e • Pi.single e 1) := by rw [map_sum]
      _ = 0 := by rw [hexpand]; exact hLq
  refine ⟨hspan_dim, hsum_pos, ?_⟩
  calc
    (∑ e : ι, (q e / ∑ f : ι, q f) • scalarColumn L e) =
        ∑ e : ι, (∑ f : ι, q f)⁻¹ • (q e • scalarColumn L e) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [div_eq_inv_mul, smul_smul]
    _ = (∑ f : ι, q f)⁻¹ • (∑ e : ι, q e • scalarColumn L e) := by
          rw [Finset.smul_sum]
    _ = 0 := by rw [hcolumns, smul_zero]

end MathlibPlus.Algebra.Claim53590
