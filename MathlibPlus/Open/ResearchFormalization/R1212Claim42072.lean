import MathlibPlus.Open.ResearchFormalization.R1212

namespace MathlibPlus.Open.ResearchFormalization.R1212Claim42072

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1212

/-- Claim 42072: under the exact singleton-nonlinear common-coordinate
profile, every nonidentity projected compatibility atom saturates its full
prime fibre under one relative-derivative orbit. -/
def everyNonidentityProjectedAtomPrimeFiberSaturated_claim42072 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (ZMod p))
      (f : Equiv.Perm (ProductGroup p)),
      oneNonlinearCommonCoordinateProfile_claim32296 q σ f →
      ∀ x : ProductGroup p, x.2 ≠ 1 →
        relativeDerivativeOrbit p f x =
          completePrimeFiber p (projectedCompatibilityAtom p f x)

end

end MathlibPlus.Open.ResearchFormalization.R1212Claim42072
