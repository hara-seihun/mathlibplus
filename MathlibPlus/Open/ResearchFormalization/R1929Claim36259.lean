import MathlibPlus.Open.FibreTranslationBatch

namespace MathlibPlus.Open.ResearchFormalization.R1929Claim36259

noncomputable section

open MathlibPlus.Open.FibreTranslation

/-- Claim 36259: for the explicit finite abelian fibre-translation subgroup,
each chosen projected component has a root holonomy subgroup, a transport
potential well defined modulo that subgroup, and exactly the displayed
holonomy-coset orbits. -/
def claim36259 : Prop :=
  ∀ (A B : Type*) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B)
    (C : FibreComponentData A B K),
    C.carrier = projectedComponent K C.basepoint ∧
      (∀ h : A,
        h ∈ C.holonomy ↔
          ∃ γ : FibreTranslationElement A B,
            γ ∈ K.carrier ∧
            γ.base C.basepoint = C.basepoint ∧
            γ.shift C.basepoint = h) ∧
      (∀ b : B, b ∈ C.carrier →
        C.transport b ∈ K.carrier ∧
          (C.transport b).base C.basepoint = b ∧
          C.potential b = (C.transport b).shift C.basepoint) ∧
      (∀ b : B, b ∈ C.carrier →
        ∀ γ δ : FibreTranslationElement A B,
          γ ∈ K.carrier → δ ∈ K.carrier →
            γ.base C.basepoint = b → δ.base C.basepoint = b →
              γ.shift C.basepoint - δ.shift C.basepoint ∈ C.holonomy) ∧
      (∀ r : A,
        fibreOrbit K (r, C.basepoint) =
          {x : A × B | ∃ b : B, ∃ h : A,
            b ∈ C.carrier ∧ h ∈ C.holonomy ∧
              x = (r + C.potential b + h, b)}) ∧
      (∀ r r' : A,
        fibreOrbit K (r, C.basepoint) = fibreOrbit K (r', C.basepoint) ↔
          r - r' ∈ C.holonomy)

end
end MathlibPlus.Open.ResearchFormalization.R1929Claim36259
