import Mathlib
import MathlibPlus.Open.ResearchFormalization.Batch_01a000fa_ef1a_7026_93c8_b04eb9d2c830

namespace MathlibPlus.Open.ResearchFormalization.Claim45771

open MathlibPlus.Open.ResearchFormalization.Batch01

/-- The simple ordinary-undirected Cayley relation in the displayed
`Cₙ ⋊ C₄` presentation. -/
def cayleyAdj (n : ℕ) (S : Set (r3035Q4n n))
    (x y : r3035Q4n n) : Prop :=
  x ≠ y ∧ r3035CayleyRelation n S x y

/-- An isomorphism of two ordinary undirected Cayley graphs on the same
presented generalized-quaternion carrier. -/
def cayleyGraphIsomorphism (n : ℕ)
    (S T : Set (r3035Q4n n)) : Prop :=
  ∃ e : Equiv.Perm (r3035Q4n n),
    ∀ x y, cayleyAdj n S x y ↔ cayleyAdj n T (e x) (e y)

/-- A group automorphism of the displayed generalized-quaternion
presentation, with the operation kept explicit rather than inferred from a
quotient or an abstract callback. -/
def q4nAutomorphism (n : ℕ) (f : r3035Q4n n → r3035Q4n n) : Prop :=
  Function.Bijective f ∧
    f (r3035QIdentity n) = r3035QIdentity n ∧
    ∀ x y, f (r3035QMul n x y) =
      r3035QMul n (f x) (f y)

/-- Transport of a connection set by an actual automorphism of `Q₄ₙ`. -/
def connectionSetTransported (n : ℕ)
    (S T : Set (r3035Q4n n)) : Prop :=
  ∃ f : r3035Q4n n → r3035Q4n n,
    q4nAutomorphism n f ∧ ∀ x, x ∈ S ↔ f x ∈ T

/-- The ordinary undirected CI property for one identity-free
inverse-closed connection set. -/
def ordinaryCI (n : ℕ) (S : Set (r3035Q4n n)) : Prop :=
  ∀ T : Set (r3035Q4n n),
    r3035ConnectionSet n T →
    cayleyGraphIsomorphism n S T →
    connectionSetTransported n S T

/-- Membership in the full graph automorphism group.  This is stated
pointwise, rather than replacing it by arbitrary symmetric-group conjugacy. -/
def graphAutomorphism (n : ℕ) (S : Set (r3035Q4n n))
    (c : Equiv.Perm (r3035Q4n n)) : Prop :=
  ∀ x y, cayleyAdj n S x y ↔ cayleyAdj n S (c x) (c y)

/-- A regular copy of the presented `Q₄ₙ` inside the full automorphism group
of the ordinary Cayley graph. -/
def regularQ4nCopy (n : ℕ) (S : Set (r3035Q4n n))
    (R : Subgroup (Equiv.Perm (r3035Q4n n))) : Prop :=
  (∀ r : R, graphAutomorphism n S r.1) ∧
  (∀ x y : r3035Q4n n, ∃! r : R, r.1 x = y) ∧
  ∃ e : r3035Q4n n ≃ R,
    ∀ x y,
      e (r3035QMul n x y) = e x * e y

/-- Conjugacy of two regular copies in the full graph automorphism group. -/
def conjugateRegularQ4nCopies (n : ℕ) (S : Set (r3035Q4n n))
    (R T : Subgroup (Equiv.Perm (r3035Q4n n))) : Prop :=
  ∃ c : Equiv.Perm (r3035Q4n n),
    graphAutomorphism n S c ∧
    ∀ r : Equiv.Perm (r3035Q4n n),
      r ∈ R ↔ c * r * c⁻¹ ∈ T

/-- Claim 45771: the all-order ordinary-undirected CI theorem and its
regular-subgroup formulation.  No directed/ DCI assertion is included. -/
def claim45771 : Prop :=
  ∀ n : ℕ,
    r3035ResidualParameter n →
    ∀ S : Set (r3035Q4n n),
      r3035ConnectionSet n S →
      ordinaryCI n S ∧
      (∀ R T : Subgroup (Equiv.Perm (r3035Q4n n)),
        regularQ4nCopy n S R →
        regularQ4nCopy n S T →
        conjugateRegularQ4nCopies n S R T)

end MathlibPlus.Open.ResearchFormalization.Claim45771
