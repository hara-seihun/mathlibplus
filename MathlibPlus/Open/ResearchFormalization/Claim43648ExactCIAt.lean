import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim43648

noncomputable section

/-- The ordinary undirected right-Cayley graph on the exact multiplicative
connection-set carrier. -/
def rightCayleyGraph43648 {G : Type*} [Group G]
    (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => x⁻¹ * y ∈ S)

/-- Inverse closure for a finite multiplicative connection set. -/
def inverseClosed43648 {G : Type*} [Group G]
    (S : Finset G) : Prop :=
  ∀ x : G, x ∈ S ↔ x⁻¹ ∈ S

def identityFree43648 {G : Type*} [Group G]
    (S : Finset G) : Prop :=
  (1 : G) ∉ S

/-- Claim 43648: the exact ordinary-undirected CI condition at valency `k`,
with no connectedness assumption, is graph-isomorphism equivalence to one
full group-automorphism image among all inverse-closed identity-free sets. -/
def claim43648 : Prop :=
  ∀ (G : Type*) [Fintype G] [DecidableEq G] [Group G]
    (k : ℕ) (S T : Finset G),
    S.card = k →
    T.card = k →
    identityFree43648 S →
    identityFree43648 T →
    inverseClosed43648 S →
    inverseClosed43648 T →
      (Nonempty (SimpleGraph.Iso
          (rightCayleyGraph43648 (S : Set G))
          (rightCayleyGraph43648 (T : Set G))) ↔
        ∃ α : G ≃* G,
          T = S.map α.toEquiv.toEmbedding)

end

end MathlibPlus.Open.ResearchFormalization.Claim43648
