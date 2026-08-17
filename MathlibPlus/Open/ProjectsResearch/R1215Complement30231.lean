import MathlibPlus.Open.ProjectsResearch.R1215
import MathlibPlus.Open.ProjectsResearch.CayleyCIClaims

namespace MathlibPlus.Open.ProjectsResearch.R1215Complement30231

open MathlibPlus.Open
open MathlibPlus.Open.ProjectsResearch.R1215

/-- The generalized dihedral carrier `E(C₇²,3)` with the scalar of order
three used by the retained profile. -/
abbrev E7 := vCarrier C7Squared

def omega7 : ZMod 7 := 2

/-- The inverse-closed pair of first nonidentity sections determined by a
transversal. -/
def firstSectionConnection (B : Finset C7Squared) : Set E7 :=
  {x | x.2 = (1 : ZMod 3) ∧ x.1 ∈ B} ∪
    {x | x.2 = (2 : ZMod 3) ∧
      ∃ b : C7Squared, b ∈ B ∧ x = vInv omega7 (b, (1 : ZMod 3))}

/-- The empty/complete kernel-graph choices in the normalized profile. -/
def kernelConnection (complete : Bool) : Set E7 :=
  if complete then
    {x | x.2 = (0 : ZMod 3) ∧ x.1 ≠ 0}
  else
    ∅

def fullConnection
    (complete : Bool) (B : Finset C7Squared) : Set E7 :=
  kernelConnection complete ∪ firstSectionConnection B

def planarTransversal (B : Finset C7Squared) : Prop :=
  B.card = 7 ∧ ∃ g : ZMod 7 → ZMod 7, B = transversalGraph g ∧ Planar 7 g

/-- Claim 30231: taking the complement in the first nonidentity section
produces the size-42 co-planar section, while the same group automorphism
continues to transport the complete connection set. -/
def claim_30231 : Prop :=
  ∀ (complete : Bool) (B C : Finset C7Squared),
    planarTransversal B → planarTransversal C →
      ∀ α : E7 ≃ E7,
        vAutomorphism omega7 α →
          vTransports α (fullConnection complete B)
            (fullConnection complete C) →
            (Finset.univ \ B).card = 42 ∧
              (Finset.univ \ C).card = 42 ∧
                vAutomorphism omega7 α ∧
                  vTransports α
                    (fullConnection complete (Finset.univ \ B))
                    (fullConnection complete (Finset.univ \ C))

end MathlibPlus.Open.ProjectsResearch.R1215Complement30231
