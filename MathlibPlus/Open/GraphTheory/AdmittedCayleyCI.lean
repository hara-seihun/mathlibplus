import Mathlib

namespace MathlibPlus.Open

/-- An identity-free inverse-closed connection set in an additive group. -/
def IdentityFreeInverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  S ⊆ ({0} : Set G)ᶜ ∧ ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

/-- The ordinary simple undirected Cayley graph of an additive group. -/
def ordinaryUndirectedCayleyGraph {G : Type*} [AddGroup G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y : G => y - x ∈ S)

/-- CI at a fixed connection-set cardinality for an additive finite group. -/
def CayleyCIAtCard (G : Type*) [AddGroup G] [Fintype G] (k : ℕ) : Prop :=
  ∀ (S T : Set G),
    IdentityFreeInverseClosed S →
    IdentityFreeInverseClosed T →
    Set.ncard S = k →
    Set.ncard T = k →
    SimpleGraph.Iso (ordinaryUndirectedCayleyGraph S)
      (ordinaryUndirectedCayleyGraph T) →
    ∃ α : G ≃+ G, α '' S = T

/-- Claim 60254: the valencies six and sixty-five are CI on C₂³ × C₉. -/
def cayleyCI_C2CubeC9_card6_and_card65 : Prop :=
  CayleyCIAtCard ((ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9) 6 ∧
    CayleyCIAtCard ((ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9) 65

/-- Claim 60257: the complement-six valencies are CI for ranks three through five. -/
def cayleyCI_C2PowC9_complement6 : Prop :=
  ∀ r : ℕ, r ∈ ({3, 4, 5} : Set ℕ) →
    let G := (Fin r → ZMod 2) × ZMod 9
    ∀ (S T : Set G),
      IdentityFreeInverseClosed S →
      IdentityFreeInverseClosed T →
      Set.ncard S = Fintype.card G - 6 →
      SimpleGraph.Iso (ordinaryUndirectedCayleyGraph S)
        (ordinaryUndirectedCayleyGraph T) →
      ∃ α : G ≃+ G, α '' S = T

/-- The identity-free inverse-closed condition for a multiplicative group. -/
def IdentityFreeInverseClosedMul {G : Type*} [Group G] (S : Set G) : Prop :=
  S ⊆ ({1} : Set G)ᶜ ∧ ∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S

/-- The ordinary simple undirected Cayley graph of a multiplicative group. -/
def ordinaryUndirectedCayleyGraphMul {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y : G => x⁻¹ * y ∈ S)

abbrev EC35_8Relators : Set (FreeGroup (Fin 2)) :=
  { (FreeGroup.of (0 : Fin 2)) ^ 35,
    (FreeGroup.of (1 : Fin 2)) ^ 8,
    FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
        (FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of (0 : Fin 2) }

abbrev EC35_8 := PresentedGroup EC35_8Relators

abbrev EC35_8_a : EC35_8 := PresentedGroup.of (0 : Fin 2)

abbrev EC35_8_t : EC35_8 := PresentedGroup.of (1 : Fin 2)

def EC35_8_rotationSubgroup : Subgroup EC35_8 :=
  Subgroup.closure ({EC35_8_a} : Set EC35_8)

/-- Claim 60255: the rotation-supported subfamily of E(C₃₅, 8) is CI. -/
def rotationSupportedSubfamily_EC35_8 : Prop :=
  ∀ (S T : Set EC35_8),
    S ⊆ (EC35_8_rotationSubgroup : Set EC35_8) \ {1} →
    T ⊆ (EC35_8_rotationSubgroup : Set EC35_8) \ {1} →
    IdentityFreeInverseClosedMul S →
    IdentityFreeInverseClosedMul T →
    SimpleGraph.Iso (ordinaryUndirectedCayleyGraphMul S)
      (ordinaryUndirectedCayleyGraphMul T) →
    ∃ α : EC35_8 ≃* EC35_8, ∃ u : (ZMod 35)ˣ,
      α EC35_8_a = EC35_8_a ^ u.val.val ∧
      α EC35_8_t = EC35_8_t ∧
      α '' S = T

end MathlibPlus.Open
