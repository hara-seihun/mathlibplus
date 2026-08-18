import MathlibPlus.Open.ResearchFormalization.R0345

namespace MathlibPlus.Open.ResearchFormalization.R0345Claim20190

open MathlibPlus.Open.Combinatorics.TreeAttachment
open MathlibPlus.Open.ResearchFormalization.R0345

noncomputable section

/-- Claim 20190: two leaf attachments of a fixed finite tree card are
isomorphic exactly when their attachment vertices lie in one automorphism
orbit of the card. -/
def claim20190_equalTreeLeafExtensionsExactlyVertexOrbits : Prop :=
  ∀ n (C : FiniteTree n) (u v : Vertex n),
    equalUnlabelledLeafExtension C u v ↔
      automorphismOrbitStep C u v

end

end MathlibPlus.Open.ResearchFormalization.R0345Claim20190
