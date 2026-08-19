import MathlibPlus.Open.Analysis.BatchO0313Claim15307

namespace MathlibPlus.Open.Analysis.BatchO0313Claim15301

open MathlibPlus.Open.Analysis.BatchO0313Claim15307
open MathlibPlus.Open.NewResearch2.PeriodicZetaFiber

noncomputable section

/-- The singular-inner Cayley coordinate and its geometric progression on the
critical line. -/
def claim15301 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    let L : ℝ := qLog q
    let r : ℝ := qRadius q
    let Φq : ℂ → ℂ := qPhi q
    singularInner15307 q ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        let s : ℂ := 1 / (1 - z)
        Φq z =
            Complex.exp ((L : ℂ) * ((1 / 2 : ℂ) - s)) ∧
          Φq z =
            Complex.exp (-((L : ℂ) / 2) * ((1 + z) / (1 - z)))) ∧
      Φq 0 = (r : ℂ) ∧
      (∀ t : ℝ,
        let z : ℂ := qCriticalPoint t
        let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
        let w : ℂ := Complex.exp (-s * (L : ℂ))
        1 / (1 - z) = s ∧
          Φq z =
            Complex.exp (-Complex.I * ((L * t : ℝ) : ℂ)) ∧
          w = (r : ℂ) * Φq z ∧
          ‖w‖ = r)

end

end MathlibPlus.Open.Analysis.BatchO0313Claim15301
