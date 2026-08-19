import MathlibPlus.Open.ResearchFormalization.R1212

namespace MathlibPlus.Open.ResearchFormalization.R1212SingletonSupport42068

open MathlibPlus.Open.ResearchFormalization.R1212

noncomputable section

/-- Claim 42068: in the exact normalized common-coordinate profile with one
nonlinear chart supported at `a`, every nonidentity source base sends `a` to
a different base, and the chart at that product base is a translation. -/
def claim42068 : Prop :=
  ∀ (p : ℕ) (q : Equiv.Perm A4)
    (σ : A4 → Equiv.Perm (ZMod p))
    (f : Equiv.Perm (ProductGroup p)) (a h : A4),
    normalizedCommonCoordinateMap q σ f →
      singletonNonlinearChart σ a →
        h ≠ 1 →
          h * a ≠ a ∧
            MathlibPlus.Open.Research.isTranslation p (σ (h * a))

end

end MathlibPlus.Open.ResearchFormalization.R1212SingletonSupport42068
