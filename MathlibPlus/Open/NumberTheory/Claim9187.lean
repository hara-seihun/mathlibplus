import Mathlib
import MathlibPlus.Open.NumberTheory.Claim9192

namespace MathlibPlus.Open.NumberTheory.Claim9187

open MathlibPlus.Open.NumberTheory.Claim9192

noncomputable def onlyDistinguishedBlockContainsExteriorRoots : Prop :=
  ∀ α : ℂ,
    replicationOne α →
      exteriorRoots α ∈ exteriorOrbit α ∧
        ∀ B : Finset ℂ,
          B ∈ exteriorOrbit α →
            B ≠ exteriorRoots α →
              ∀ z : ℂ, z ∈ B → z ∉ exteriorRoots α

end MathlibPlus.Open.NumberTheory.Claim9187
