import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim23419

def privateComponentSignaturesGiveColumnIndependence : Prop :=
  ∀ {Row Component K : Type*}
    [Fintype Row] [Fintype Component] [DecidableEq Component]
    [Field K]
    (matrix : Row → Component → K)
    (privateRow : Component → Row),
    (∀ component : Component,
      matrix (privateRow component) component ≠ 0 ∧
        ∀ other : Component, other ≠ component →
          matrix (privateRow component) other = 0) →
      LinearIndependent K (fun component : Component =>
        fun row : Row => matrix row component)

end MathlibPlus.Open.ResearchFormalization.Claim23419
