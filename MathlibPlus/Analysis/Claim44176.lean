import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim44176

/-- Distinct positive shifts give distinct retained inverse-power weights at every
positive support point.  The source's type-2 transform conclusion is left at
its original interface; this is its pointwise algebraic core. -/
theorem retained_weight_ne
    {u v₁ v₂ : ℝ} {k : ℕ}
    (hu : 0 < u) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hk : 0 < k) (hvv : v₁ ≠ v₂) :
    ((u + v₁) ^ k)⁻¹ ≠ ((u + v₂) ^ k)⁻¹ := by
  have h₁ : 0 < u + v₁ := by linarith
  have h₂ : 0 < u + v₂ := by linarith
  have hbase : u + v₁ ≠ u + v₂ := by
    intro heq
    apply hvv
    linarith
  have hpow : (u + v₁) ^ k ≠ (u + v₂) ^ k := by
    intro h
    have hle : u + v₁ ≤ u + v₂ ∨ u + v₂ ≤ u + v₁ := le_total _ _
    rcases hle with hle | hle
    · have : u + v₁ = u + v₂ := by
        apply le_antisymm hle
        exact le_of_not_gt (by
          intro hgt
          have hp : (u + v₁) ^ k < (u + v₂) ^ k :=
            pow_lt_pow_left₀ hgt (le_of_lt h₁) hk.ne'
          exact (ne_of_gt hp) h.symm)
      exact hbase this
    · have : u + v₂ = u + v₁ := by
        apply le_antisymm hle
        exact le_of_not_gt (by
          intro hgt
          have hp : (u + v₂) ^ k < (u + v₁) ^ k :=
            pow_lt_pow_left₀ hgt (le_of_lt h₂) hk.ne'
          exact (ne_of_gt hp) h)
      exact hbase this.symm
  intro h
  exact hpow (inv_injective h)

end MathlibPlus.Analysis.Claim44176
