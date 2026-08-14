import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research

/-- A concrete group model for `C_p × A₄`. -/
abbrev CpA4 (p : ℕ) := Multiplicative (ZMod p) × (alternatingGroup (Fin 4))

/-- Connection-set hypotheses for a simple undirected Cayley relation. -/
def undirectedConnection {G : Type*} [Group G] (S : Set G) : Prop :=
  (1 : G) ∉ S ∧ ∀ s : G, s ∈ S → s⁻¹ ∈ S

/-- An isomorphism between the two Cayley relations determined by `S` and `T`. -/
def cayleyRelationIso {G : Type*} [Group G]
    (S T : Set G) (f : G → G) : Prop :=
  Function.Bijective f ∧
    ∀ x y : G, (x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T)

/-- CI means that every Cayley-relation isomorphism has a group-automorphism
connection-set image. -/
def claim30721 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 13 ≤ p →
    ∀ S T : Set (CpA4 p),
      undirectedConnection S →
      undirectedConnection T →
      (∃ f : CpA4 p → CpA4 p, cayleyRelationIso S T f) →
      ∃ φ : CpA4 p ≃* CpA4 p, ∀ x : CpA4 p, x ∈ S ↔ φ x ∈ T

/-- The permutation group induced on a block by a subgroup of an acting group. -/
def inducedPermGroup {U B : Type*} [Group U] [MulAction U B]
    (K : Subgroup U) : Subgroup (Equiv.Perm B) :=
  ((MulAction.toPermHom U B).comp K.subtype).range

/-- A subgroup acts transitively on the block through the ambient action. -/
def actsTransitivelyOn {U B : Type*} [Group U] [MulAction U B]
    (K : Subgroup U) : Prop :=
  ∀ b₁ b₂ : B, ∃ k : K, (k : U) • b₁ = b₂

/-- A finite `p`-group acting on a `p`-point block has at most `p` induced
permutations; transitive induced subgroups of order `p` coincide. -/
def claim30723 : Prop :=
  ∀ (p : ℕ) (U B : Type*) [Group U] [Finite U] [Fintype B]
    [MulAction U B] (P Q : Subgroup U),
    Nat.Prime p →
    IsPGroup p U →
    Nat.card B = p →
    Nat.card (inducedPermGroup (U := U) (B := B) (⊤ : Subgroup U)) ≤ p ∧
      (Nat.card (inducedPermGroup (U := U) (B := B) P) = p →
        Nat.card (inducedPermGroup (U := U) (B := B) Q) = p →
        actsTransitivelyOn (U := U) (B := B) P →
        actsTransitivelyOn (U := U) (B := B) Q →
        inducedPermGroup (U := U) (B := B) P =
          inducedPermGroup (U := U) (B := B) Q)

end MathlibPlus.Open.Research
