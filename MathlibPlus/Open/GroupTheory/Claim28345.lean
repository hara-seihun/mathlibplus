import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim28345

noncomputable section

def preservesSubgroup
    {G : Type*} [Group G] (N : Subgroup G) (alpha : G ≃* G) : Prop :=
  Set.image (alpha : G → G) (N : Set G) = (N : Set G)

def descendedFormula
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (alpha : G ≃* G) (beta : (G ⧸ N) ≃* (G ⧸ N)) : Prop :=
  ∀ g : G,
    beta (QuotientGroup.mk' N g) = QuotientGroup.mk' N (alpha g)

def nonWellDefinedExample : Prop :=
  let G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  let N : Subgroup G :=
    (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤
  let alpha : G ≃* G := MulEquiv.prodComm
  ∃ g h : G,
    QuotientGroup.mk' N g = QuotientGroup.mk' N h ∧
      QuotientGroup.mk' N (alpha g) ≠ QuotientGroup.mk' N (alpha h)

/-- Claim 28345: preservation of a normal subgroup is exactly the condition
needed for the induced quotient automorphism, and the unpreserved formula can
fail to be well-defined. -/
def claim28345 : Prop :=
  (∀ (G : Type*) [Fintype G] [Group G]
      (N : Subgroup G) [N.Normal] (alpha : G ≃* G),
      (preservesSubgroup N alpha ↔
        ∀ n : G, n ∈ N → alpha n ∈ N) ∧
      (preservesSubgroup N alpha →
        ∃ beta : (G ⧸ N) ≃* (G ⧸ N),
          descendedFormula N alpha beta)) ∧
    nonWellDefinedExample

end
end MathlibPlus.Open.GroupTheory.Claim28345
