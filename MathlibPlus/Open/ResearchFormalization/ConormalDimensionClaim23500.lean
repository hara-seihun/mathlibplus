import MathlibPlus.Open.Research.ScalarConormalClaims26426_26428

namespace MathlibPlus.Open.ResearchFormalization

open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

/-- Claim 23500: the degree-`n` piece of the exact scalar conormal module has
    the displayed `s^b z^a e_k` basis and binomial dimension. -/
def claim_23500 : Prop :=
  letI : Module (Polynomial ℚ) scalarConormalA :=
    Module.compHom scalarConormalA scalarPolyToAQuotient.toRingHom
  ∃ e : scalarConormalA ≃ₗ[Polynomial ℚ]
      ((ScalarKernelIndex × ℕ) →₀ Polynomial ℚ),
    (∀ k : ScalarKernelIndex, ∀ a : ℕ,
      e (scalarConormalAGenerator k a) = Finsupp.single (k, a) 1) ∧
    (∀ n : ℕ,
      Module.finrank ℚ (scalarConormalDegree e n) = Nat.choose n 2)

end
end MathlibPlus.Open.ResearchFormalization
