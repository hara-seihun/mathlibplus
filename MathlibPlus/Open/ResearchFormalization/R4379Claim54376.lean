import MathlibPlus.Open.ResearchFormalization.R4379Claim54378

namespace MathlibPlus.Open.ResearchFormalization.R4379Claim54376

open scoped BigOperators

/--
R-4379.1: contracting a positive scalar circuit to any nonempty subset of its
support preserves the stated quotient rank and positive scalar-circuit data.
-/
def canonicalContractionToSupportSubset {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (q : E → ℚ) (S : Finset E) : Prop :=
  MathlibPlus.Open.ResearchFormalization.R4379Claim54378.positiveScalarCircuit L q S →
    ∀ T : Finset E, T.Nonempty → ∀ hTS : T ⊆ S,
      Module.finrank ℚ
          (MathlibPlus.Open.ResearchFormalization.R4379Claim54378.contractionQuotient
            L S T) = T.card - 1 ∧
        Submodule.span ℚ
            (Set.range (fun e : {e : E // e ∈ T} =>
              MathlibPlus.Open.ResearchFormalization.R4379Claim54378.contractionColumn
                L S T hTS e)) = ⊤ ∧
        LinearMap.ker
              (MathlibPlus.Open.ResearchFormalization.R4379Claim54378.contractionMap
                L S T hTS) =
          Submodule.span ℚ (Set.singleton (fun e : {e : E // e ∈ T} =>
            q e / ∑ f ∈ S, q f)) ∧
        Module.finrank ℚ
            (LinearMap.ker
              (MathlibPlus.Open.ResearchFormalization.R4379Claim54378.contractionMap
                L S T hTS)) = 1 ∧
        (∀ e : {e : E // e ∈ T}, 0 < q e / ∑ f ∈ S, q f) ∧
        MathlibPlus.Open.ResearchFormalization.R4379Claim54378.positiveScalarCircuit
          (MathlibPlus.Open.ResearchFormalization.R4379Claim54378.contractionMap
            L S T hTS)
          (fun e : {e : E // e ∈ T} =>
            (q e / ∑ f ∈ S, q f) /
              ∑ f : {f : E // f ∈ T}, q f / ∑ g ∈ S, q g)
          Finset.univ

end MathlibPlus.Open.ResearchFormalization.R4379Claim54376
