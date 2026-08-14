import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

section Cayley

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def cayleyRelation (S : Set G) (x y : G) : Prop := x⁻¹ * y ∈ S

def inverseClosedConnection (S : Set G) : Prop :=
  ∀ ⦃s : G⦄, s ∈ S → s⁻¹ ∈ S

def looplessConnection (S : Set G) : Prop := 1 ∉ S

def normalizedCayleyIsomorphism (S T : Set G) (e : Equiv.Perm G) : Prop :=
  e 1 = 1 ∧ ∀ x y : G,
    cayleyRelation S x y ↔ cayleyRelation T (e x) (e y)

def automorphismTransportsConnection (S T : Set G) (α : G ≃* G) : Prop :=
  ∀ s : G, s ∈ S ↔ α s ∈ T

/-- The identity-normalized connection-set form of the graph-CI predicate. -/
def graphCI (H : Type*) [Group H] [Fintype H] [DecidableEq H] : Prop :=
  ∀ (S T : Set H) (e : Equiv.Perm H),
    inverseClosedConnection S → inverseClosedConnection T →
      looplessConnection S → looplessConnection T →
        normalizedCayleyIsomorphism S T e →
          ∃ α : H ≃* H, automorphismTransportsConnection S T α

/-- The directed version drops inverse-closure of the connection sets. -/
def digraphDCI (H : Type*) [Group H] [Fintype H] [DecidableEq H] : Prop :=
  ∀ (S T : Set H) (e : Equiv.Perm H),
    normalizedCayleyIsomorphism S T e →
      ∃ α : H ≃* H, automorphismTransportsConnection S T α

/-- Claim 28335: graph-CI and DCI are the two connection-set predicates. -/
def graphCIAndDigraphDCIPredicates : Prop :=
  (∀ (H : Type*) [Group H] [Fintype H] [DecidableEq H],
      graphCI H =
        (∀ (S T : Set H) (e : Equiv.Perm H),
          inverseClosedConnection S → inverseClosedConnection T →
            looplessConnection S → looplessConnection T →
              normalizedCayleyIsomorphism S T e →
                ∃ α : H ≃* H, automorphismTransportsConnection S T α)) ∧
    (∀ (H : Type*) [Group H] [Fintype H] [DecidableEq H],
      digraphDCI H =
        (∀ (S T : Set H) (e : Equiv.Perm H),
          normalizedCayleyIsomorphism S T e →
            ∃ α : H ≃* H, automorphismTransportsConnection S T α))

/-- Claim 28337: graph-CI is hereditary to subgroups. -/
def graphCIHereditaryToSubgroups : Prop :=
  ∀ (H : Type*) [Group H] [Fintype H] [DecidableEq H],
    graphCI H → ∀ K : Subgroup H, (let _ := Fintype.ofFinite K; graphCI K)

/-- Claim 28339: DCI descends through normal quotients. -/
def dciHereditaryToNormalQuotients : Prop :=
  ∀ (H : Type*) [Group H] [Fintype H] [DecidableEq H],
    ∀ N : Subgroup H, ∀ hN : N.Normal,
      digraphDCI H →
        (let _ : N.Normal := hN;
          let _ : DecidableEq (H ⧸ N) := Classical.decEq _;
          let _ := Fintype.ofFinite (H ⧸ N);
          digraphDCI (H ⧸ N))

end Cayley

end MathlibPlus.Open.ResearchFormalization
