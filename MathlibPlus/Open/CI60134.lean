import Mathlib

namespace MathlibPlus.Open.CI60134

def IdentityFree {G : Type*} [Group G] (S : Set G) : Prop :=
  S ⊆ (Set.univ : Set G) \ {1}

def InverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S ↔ x⁻¹ ∈ S

def CayleyGraphIsomorphism {G : Type*} [Group G]
    (S T : Set G) : Prop :=
  ∃ f : G → G,
    Function.Bijective f ∧
      ∀ x y : G, (x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T)

def OrdinaryUndirectedCIConnectionSet {G : Type*} [Group G]
    (S : Set G) : Prop :=
  IdentityFree S ∧
    InverseClosed S ∧
      ∀ T : Set G,
        IdentityFree T →
          InverseClosed T →
            CayleyGraphIsomorphism S T →
              ∃ α : G ≃* G, α '' S = T

abbrev C4 := Multiplicative (ZMod 4)
abbrev G (V : Type*) := C4 × V

def centralInvolutionLayer (V : Type*) [Group V] : Set (G V) :=
  {Multiplicative.ofAdd (2 : ZMod 4)} ×ˢ (Set.univ : Set V)

def centralInvolutionComplement (V : Type*) [Group V] : Set (G V) :=
  ((Set.univ : Set (G V)) \ {(1 : G V)}) \ centralInvolutionLayer V

def claim60134 (V : Type*) [Group V] [Fintype V] : Prop :=
  Odd (Fintype.card V) →
    OrdinaryUndirectedCIConnectionSet (centralInvolutionLayer V) ∧
      OrdinaryUndirectedCIConnectionSet (centralInvolutionComplement V) ∧
        ∀ R T : Set (G V),
          (R = centralInvolutionLayer V ∨
              R = centralInvolutionComplement V) →
            IdentityFree T →
              InverseClosed T →
                CayleyGraphIsomorphism R T →
                  T = R

end MathlibPlus.Open.CI60134
