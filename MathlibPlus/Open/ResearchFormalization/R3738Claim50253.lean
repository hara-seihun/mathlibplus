import MathlibPlus.Open.ResearchFormalization.R3738Claim50252

namespace MathlibPlus.Open.ResearchFormalization.R3738Claim50253

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R3738Claim50252

/-- Claim 50253: the S2 first-normal equations and their exact elimination
coupling, using the normal (epsilon) constant specialization. -/
def claim50253_exactNormalCoupling : Prop :=
  ∀ (R : Type*) [CommRing R] [IsDomain R]
    (E : RootedPolynomial R) (t u r v : R),
    u ≠ 0 → r ≠ 0 → t - u ≠ 0 →
      baseSelectorKernel t u r v E →
        (baseSpecialization t u r v v E +
            u * normalSpecialization t u r v r E +
            (t - u) * normalConstantSpecialization t u r v E = 0) ∧
          (v * baseSpecialization t u r v v E +
              u * r * normalSpecialization t u r v r E = 0) ∧
          (v - r) * baseSpecialization t u r v v E =
            r * (t - u) * normalConstantSpecialization t u r v E

end

end MathlibPlus.Open.ResearchFormalization.R3738Claim50253
