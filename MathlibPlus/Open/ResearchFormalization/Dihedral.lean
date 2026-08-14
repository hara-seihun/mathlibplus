import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Dihedral

noncomputable section

abbrev D16 := DihedralGroup 8

def r : D16 := DihedralGroup.r (1 : ZMod 8)

def s : D16 := DihedralGroup.sr (0 : ZMod 8)

def dihedralPresentation : Prop :=
  Fintype.card D16 = 16 ∧ r ^ 8 = 1 ∧ s ^ 2 = 1 ∧ s * r * s = r⁻¹

def S₀ : Finset D16 := {r, r⁻¹, s, r ^ 4 * s}
def S₁ : Finset D16 := {s, r * s, r ^ 3 * s, r ^ 4 * s}
def S₂ : Finset D16 := {s, r * s, r ^ 2 * s, r ^ 5 * s}

def inverseClosed (S : Finset D16) : Prop :=
  ∀ g, g ∈ S → g⁻¹ ∈ S

def generatesD16 (S : Finset D16) : Prop :=
  Subgroup.closure (S : Set D16) = ⊤

def cayleyAdj (S : Finset D16) (g h : D16) : Prop := g⁻¹ * h ∈ S

def connectedUndirectedFourRegularCayley (S : Finset D16) : Prop := by
  classical
  exact inverseClosed S ∧ 1 ∉ S ∧ S.card = 4 ∧ generatesD16 S ∧
    (∀ g : D16, (Finset.univ.filter (fun h => cayleyAdj S g h)).card = 4)

def claim_24230 : Prop :=
  dihedralPresentation ∧
    (∀ S : Finset D16, S = S₀ ∨ S = S₁ ∨ S = S₂ →
      inverseClosed S ∧ generatesD16 S ∧ S.card = 4 ∧
        connectedUndirectedFourRegularCayley S)

def automorphismOrbit (S : Finset D16) : Set (Set D16) :=
  {T | ∃ φ : D16 ≃* D16, T = φ '' (S : Set D16)}

def claim_24232 : Prop :=
  automorphismOrbit S₀ ≠ automorphismOrbit S₁ ∧
    automorphismOrbit S₀ ≠ automorphismOrbit S₂ ∧
    automorphismOrbit S₁ ≠ automorphismOrbit S₂ ∧
    (∀ i j : Fin 3, i ≠ j →
      ¬ ∃ φ : D16 ≃* D16,
        φ '' ((![S₀, S₁, S₂] i : Finset D16) : Set D16) =
          ((![S₀, S₁, S₂] j : Finset D16) : Set D16))

end

end MathlibPlus.Open.ResearchFormalization.Dihedral
