import Mathlib

namespace MathlibPlus.Open.CI60131

def AddIdentityFree {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  S ⊆ (Set.univ : Set G) \ {0}

def AddInverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S ↔ -x ∈ S

def AddCayleyGraphIsomorphism {G : Type*} [AddGroup G]
    (S T : Set G) : Prop :=
  ∃ f : G → G,
    Function.Bijective f ∧
      ∀ x y : G, (y - x ∈ S ↔ f y - f x ∈ T)

def AddOrdinaryUndirectedCIConnectionSet {G : Type*} [AddGroup G]
    (S : Set G) : Prop :=
  AddIdentityFree S ∧
    AddInverseClosed S ∧
      ∀ T : Set G,
        AddIdentityFree T →
          AddInverseClosed T →
            AddCayleyGraphIsomorphism S T →
              ∃ α : G ≃+ G, α '' S = T

abbrev K := ZMod 4
abbrev V := Fin 3 → ZMod 3
abbrev G := K × V

def radialConnection (U : Set V) : Set G :=
  Set.univ ×ˢ U

def centralConnection (U : Set V) : Set G :=
  ((Set.univ : Set K) \ {0}) ×ˢ ({0} : Set V) ∪ Set.univ ×ˢ U

def claim60131 : Prop :=
  ∀ U : Set V,
    U ⊆ (Set.univ : Set V) \ {0} →
      AddInverseClosed U →
        AddOrdinaryUndirectedCIConnectionSet (radialConnection U) ∧
          AddOrdinaryUndirectedCIConnectionSet (centralConnection U)

end MathlibPlus.Open.CI60131
