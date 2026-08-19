import Mathlib
import MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims47814_47818

namespace MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims47812Formalization

open Classical

/-- Claim 47812: the occurrence-sensitive integer leaf-deletion incidence has
positive support exactly at the parent extensions of a card; repeated cards
remain multiplicities while support forgets those multiplicities. -/
def claim47812 : Prop :=
  ∀ (n : ℕ)
    (P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1))
    (H : MathlibPlus.Open.Combinatorics.UnlabelledTree n),
    (H ∈ MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims.leafSupport P ↔
        0 < MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims.leafCardMultiplicity P H) ∧
      (H ∈ MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims.leafSupport P ↔
        P ∈ MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims.extensionSet H)

end MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims47812Formalization
