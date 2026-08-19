import MathlibPlus.Open.ResearchFormalization.R1212

namespace MathlibPlus.Open.ResearchFormalization.R1212SingletonSupport

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1212

/-- Claim 32297: a nonidentity singleton support in the exact A4 base has
trivial left stabilizer, and every nonidentity source base sends the unique
nonlinear chart to a translation chart. -/
def singletonSupportTrivialLeftStabilizer_claim32297 : Prop :=
  (∀ (a h : A4), a ≠ 1 → h ≠ 1 → h * a ≠ a) ∧
    ∀ (p : ℕ) (σ : A4 → Equiv.Perm (ZMod p)) (a : A4),
      singletonNonlinearChart σ a →
        ∀ h : A4, h ≠ 1 →
          h * a ≠ a ∧
            MathlibPlus.Open.Research.isTranslation p (σ (h * a))

end

end MathlibPlus.Open.ResearchFormalization.R1212SingletonSupport
