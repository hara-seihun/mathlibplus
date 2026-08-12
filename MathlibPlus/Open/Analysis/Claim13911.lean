import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace MathlibPlus.Open.Analysis.Claim13911

/-- The source's assertion that the free Neumann cosine is the unique solution
of the initial-value problem, with the interval and derivative interface made
explicit.  This is a registry node because the source packet does not supply a
kernel-checked uniqueness proof in this interface. -/
def freeNeumannIVPUniqueness : Prop :=
  ∀ (a z lam : ℝ), 0 < a → z ^ 2 = lam →
    ∀ (u w : ℝ → ℝ),
      u 0 = 1 →
        w 0 = 0 →
          (∀ x ∈ Set.Icc 0 a,
            HasDerivAt u (w x) x ∧
              HasDerivAt w (-lam * u x) x) →
            ∀ x ∈ Set.Icc 0 a,
              u x = Real.cos (z * x) ∧
                w x = -z * Real.sin (z * x)

end MathlibPlus.Open.Analysis.Claim13911
