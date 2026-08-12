import Mathlib

namespace MathlibPlus.Analysis.Claim19058

noncomputable section

/--
Claim 19058.  A finite positive reciprocal-scale mixture of a kernel
satisfying the centered reciprocal relation satisfies that relation again.
The finite mixture is represented by a `Fintype` index, and the source's
notation `x ^ (-1/2)` is interpreted as `Real.rpow`.
-/
theorem reciprocalScaleModular
    {ι : Type*} [Fintype ι]
    (θ : ℝ → ℝ)
    (hθ : ∀ x, 0 < x →
      θ x = x ^ (-1 / 2 : ℝ) * θ x⁻¹)
    (c₀ : ℝ) (c : ι → ℝ) (a : ι → ℝ)
    (_hc₀ : 0 < c₀) (_hc : ∀ i, 0 < c i) (ha : ∀ i, 0 < a i) :
    ∀ x, 0 < x →
      (c₀ * θ x +
          ∑ i, c i *
            (θ (a i * x) + (a i) ^ (-1 / 2 : ℝ) * θ (x / a i))) =
        x ^ (-1 / 2 : ℝ) *
          (c₀ * θ x⁻¹ +
            ∑ i, c i *
              (θ (a i * x⁻¹) + (a i) ^ (-1 / 2 : ℝ) *
                θ (x⁻¹ / a i))) := by
  classical
  let q : ℝ → ℝ := fun y => y ^ (-1 / 2 : ℝ)
  have hθq : ∀ y, 0 < y → θ y = q y * θ y⁻¹ := by
    intro y hy
    simpa [q] using hθ y hy
  have q_pos : ∀ y, 0 < y → 0 < q y := by
    intro y hy
    exact Real.rpow_pos_of_pos hy _
  have q_mul : ∀ u v, 0 < u → 0 < v → q (u * v) = q u * q v := by
    intro u v hu hv
    dsimp [q]
    rw [Real.mul_rpow (le_of_lt hu) (le_of_lt hv)]
  have q_inv : ∀ u, 0 < u → q u⁻¹ = (q u)⁻¹ := by
    intro u hu
    dsimp [q]
    rw [Real.inv_rpow (le_of_lt hu)]
  have q_div : ∀ u v, 0 < u → 0 < v →
      q (u / v) = q u * (q v)⁻¹ := by
    intro u v hu hv
    rw [div_eq_mul_inv, q_mul u v⁻¹ hu (inv_pos.mpr hv), q_inv v hv]
  have pair : ∀ u v, 0 < u → 0 < v →
      θ (u * v) + q u * θ (v / u) =
        q v * (θ (u * v⁻¹) + q u * θ (v⁻¹ / u)) := by
    intro u v hu hv
    have huv : 0 < u * v := mul_pos hu hv
    have hvu : 0 < v / u := div_pos hv hu
    have hqu : q u ≠ 0 := ne_of_gt (q_pos u hu)
    have hθuv := hθq (u * v) huv
    have hθvu := hθq (v / u) hvu
    have hquv := q_mul u v hu hv
    have hqvu := q_div v u hv hu
    have hrecipuv : (u * v)⁻¹ = v⁻¹ / u := by
      simp [div_eq_mul_inv, mul_comm]
    have hrecipvu : (v / u)⁻¹ = u * v⁻¹ := by
      simp [div_eq_mul_inv, mul_comm]
    change θ (u * v) + q u * θ (v / u) =
      q v * (θ (u * v⁻¹) + q u * θ (v⁻¹ / u))
    rw [hθuv, hθvu, hquv, hqvu, hrecipuv, hrecipvu]
    field_simp
    ring
  intro x hx
  have hθx := hθq x hx
  have hsum :
      (∑ i, c i * (θ (a i * x) + q (a i) * θ (x / a i))) =
        q x * ∑ i, c i *
          (θ (a i * x⁻¹) + q (a i) * θ (x⁻¹ / a i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pair (a i) x (ha i) hx]
    ring
  change (c₀ * θ x +
      ∑ i, c i * (θ (a i * x) + q (a i) * θ (x / a i))) =
    q x * (c₀ * θ x⁻¹ +
      ∑ i, c i * (θ (a i * x⁻¹) + q (a i) * θ (x⁻¹ / a i)))
  rw [hθx, hsum]
  ring

end
end MathlibPlus.Analysis.Claim19058
