import MathlibPlus.Open.ResearchFormalization.R0474FixedXHilbertCauchy

namespace MathlibPlus.Open.Research.R0474PoissonLaguerre21845

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0474

/-- The first-shift Poisson--Laguerre feature in the reviewed coordinate
realization. -/
def poissonLaguerreFirstShiftFeature
    (x : ℝ) (z : ℂ) : ℕ → ℂ × ℂ :=
  complexFeature_21850 x z

/-- Claim 21845: for positive fixed `x`, the zeroed Laguerre coordinates and
Poisson weights form the square-summable Hilbert feature with the first shift. -/
def claim21845_poissonLaguerreFirstShiftFeature : Prop :=
  ∀ x : ℝ, 0 < x →
    ∀ z : ℂ,
      isFeatureVector_21850 (poissonLaguerreFirstShiftFeature x z) ∧
        (∀ n : ℕ,
          let p_n : ℝ := poissonWeight_21850 x n
          let v_n : ℂ := laguerreAtomComplex n z
          let v_next : ℂ := laguerreAtomComplex (n + 1) z
          (poissonLaguerreFirstShiftFeature x z) n =
            (((Real.sqrt p_n : ℝ) : ℂ) * v_n,
              ((Real.sqrt p_n : ℝ) : ℂ) * v_next))

end

end MathlibPlus.Open.Research.R0474PoissonLaguerre21845
