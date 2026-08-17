import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1179.Claim31911

noncomputable section

abbrev C3Squared := Multiplicative (Fin 2 → ZMod 3)
abbrev D10 := DihedralGroup 5
abbrev G := C3Squared × D10

def isConnectionSet (S : Set G) : Prop :=
  (1 : G) ∉ S ∧
    ∀ g : G, g ∈ S ↔ g⁻¹ ∈ S

def cayleyGraph (S : Set G) : SimpleGraph G :=
  SimpleGraph.mulCayley S

def graphIsomorphism (S T : Set G) : Prop :=
  Nonempty ((cayleyGraph S).Iso (cayleyGraph T))

def graphAutomorphism (Γ : SimpleGraph G) (e : Equiv.Perm G) : Prop :=
  ∀ x y, Γ.Adj x y ↔ Γ.Adj (e x) (e y)

def fullGraphAutomorphismSubgroup (Γ : SimpleGraph G)
    (Aut : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ e : Equiv.Perm G, e ∈ Aut ↔ graphAutomorphism Γ e

def fiveSquareRow (S : Set G) : Prop :=
  isConnectionSet S ∧
    Set.ncard S = 10 ∧
    SimpleGraph.Connected (cayleyGraph S) ∧
    ∃ Aut : Subgroup (Equiv.Perm G),
      fullGraphAutomorphismSubgroup (cayleyGraph S) Aut ∧
        ∃ P : Sylow 5 Aut, 25 ≤ Nat.card P

/-- CI transport on the actual finite group carrier. -/
def ordinaryCI (S : Set G) : Prop :=
  isConnectionSet S ∧
    ∀ T : Set G,
      isConnectionSet T →
        graphIsomorphism S T →
          ∃ α : G ≃* G, α '' S = T

/-- Claim 31911: all five exact connected valency-ten Sylow-filtered graph
types on the displayed group have ordinary undirected CI transport. -/
def claim31911 : Prop :=
  ∃ rows : Fin 5 → Set G,
    (∀ i : Fin 5, fiveSquareRow (rows i)) ∧
    (∀ i j : Fin 5,
      graphIsomorphism (rows i) (rows j) → i = j) ∧
    (∀ S : Set G, fiveSquareRow S →
      ∃ i : Fin 5, graphIsomorphism S (rows i)) ∧
    (∀ i : Fin 5, ordinaryCI (rows i))

end

end MathlibPlus.Open.ResearchFormalization.R1179.Claim31911
