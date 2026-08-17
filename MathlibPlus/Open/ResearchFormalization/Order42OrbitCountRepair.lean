import MathlibPlus.Open.ResearchFormalization.Order42Batch

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The orbit of a finite connection set under the full additive
automorphism group of the reviewed order-42 model. -/
noncomputable def connectionSetAutomorphismOrbit
    (A : Finset Order42) : Finset (Finset Order42) :=
  (Finset.univ : Finset (Order42 ≃+ Order42)).image
    (fun φ => A.map φ.toEquiv.toEmbedding)

/-- Claim 27823: the reviewed inverse-closed connection-set carrier has the
exact raw cardinality and exact number of orbits under the full action. -/
def exactConnectionSetOrbitCount_claim27823 : Prop :=
  connectionSets.card = 4194304 ∧
    (connectionSets.image connectionSetAutomorphismOrbit).card = 156864

end

end MathlibPlus.Open.ResearchFormalization
