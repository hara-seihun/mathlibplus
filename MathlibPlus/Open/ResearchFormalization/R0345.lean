import Mathlib
import MathlibPlus.Open.Combinatorics.TreeAttachment

namespace MathlibPlus.Open.ResearchFormalization.R0345

open MathlibPlus.Open.Combinatorics.TreeAttachment

noncomputable section

/-- Equality of the two unlabelled leaf extensions of a fixed tree card. -/
def equalUnlabelledLeafExtension {n : ℕ}
    (C : FiniteTree n) (u v : Vertex n) : Prop :=
  Nonempty (attachGraph C u ≃g attachGraph C v)

/-- The automorphism relation of a fixed finite tree card. -/
def treeCardAutomorphism {n : ℕ}
    (C : FiniteTree n) (e : Equiv.Perm (Vertex n)) : Prop :=
  ∀ x y, C.1.Adj (e x) (e y) ↔ C.1.Adj x y

abbrev CardAutomorphism {n : ℕ} (C : FiniteTree n) :=
  {e : Equiv.Perm (Vertex n) // treeCardAutomorphism C e}

def automorphismOrbitStep {n : ℕ}
    (C : FiniteTree n) (u v : Vertex n) : Prop :=
  ∃ e : CardAutomorphism C, e.1 u = v

/-- The quotient of vertices by equality of their unlabelled leaf extensions. -/
abbrev AttachmentFiber {n : ℕ} (C : FiniteTree n) :=
  Quotient (Relation.EqvGen.setoid (equalUnlabelledLeafExtension C))

/-- The quotient of vertices by the automorphism orbit relation. -/
abbrev VertexOrbit {n : ℕ} (C : FiniteTree n) :=
  Quotient (Relation.EqvGen.setoid (automorphismOrbitStep C))

abbrev AttachmentFiberSpace {n : ℕ} (C : FiniteTree n) :=
  AttachmentFiber C →₀ ℚ

abbrev VertexOrbitSpace {n : ℕ} (C : FiniteTree n) :=
  VertexOrbit C →₀ ℚ

/-- For every tree card, the attachment quotient is canonically the rational
free space on the vertex orbits of its automorphism group. -/
def claim20191_fiberwiseAttachmentQuotientIsOrbitSpace : Prop :=
  ∀ n (C : FiniteTree n),
    (∀ u v : Vertex n,
      equalUnlabelledLeafExtension C u v ↔ automorphismOrbitStep C u v) ∧
      ∃! e : AttachmentFiberSpace C ≃ₗ[ℚ] VertexOrbitSpace C,
        ∀ v : Vertex n,
          e (Finsupp.single (Quotient.mk'' v) 1) =
            Finsupp.single (Quotient.mk'' v) 1

end
end MathlibPlus.Open.ResearchFormalization.R0345
