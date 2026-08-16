import Mathlib

namespace MathlibPlus.Open.Research

/-- The ordinary undirected additive Cayley graph determined by a connection set. -/
def additiveCayleyGraph {V : Type*} [AddCommGroup V] (S : Set V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => ∃ s ∈ S, y = x + s)

/-- Identity-free inverse-closedness for an additive connection set. -/
def identityFreeNegClosed {V : Type*} [AddGroup V] (S : Set V) : Prop :=
  0 ∉ S ∧ ∀ x, x ∈ S → -x ∈ S

/-- Block-axis direction-rigidity for finite direct-sum decompositions over `F_p`. -/
def blockAxisDirectionRigidity60202 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V],
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
        (U : ι → Submodule (ZMod p) V),
        (∀ i, U i ≠ ⊥) →
        DirectSum.IsInternal U →
        (∀ d : ℕ, 0 < d →
          Fintype.card {i : ι // Module.finrank (ZMod p) (U i) = d} < p) →
        let S : Set V := ⋃ i, (U i : Set V) \ {0}
        ∀ T : Set V,
          identityFreeNegClosed T →
          Nonempty (SimpleGraph.Iso (additiveCayleyGraph S)
            (additiveCayleyGraph T)) →
          ∃ L : V ≃ₗ[ZMod p] V, Set.image (L : V → V) S = T

end MathlibPlus.Open.Research
