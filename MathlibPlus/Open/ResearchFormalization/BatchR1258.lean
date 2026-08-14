import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR1258

abbrev D10 := DihedralGroup 5

def rotation : D10 := DihedralGroup.r (1 : ZMod 5)

def reflection : D10 := DihedralGroup.sr (0 : ZMod 5)

def connectionSet (A B : Type*) [Group A] [Group B] : Set (A × B × D10) :=
  {g | ∃ a : A, g = (a, 1, rotation ^ (2 : ℕ))} ∪
    {g | ∃ a : A, g = (a, 1, (rotation ^ (2 : ℕ))⁻¹)} ∪
    {g | ∃ b : B, ∃ z : D10,
      z ∈ Subgroup.closure ({reflection} : Set D10) ∧
      (b, z) ≠ (1, 1) ∧ g = (1, b, z)}

/-- The displayed Cartesian connection set in Claim 30688 is inverse-closed
and omits the identity under the stated order hypotheses. -/
def claim_30688 : Prop :=
  ∀ (A B : Type*) [Group A] [Fintype A] [Group B] [Fintype B]
    (n m : ℕ),
    Nontrivial A →
    Fintype.card A = n → Odd n →
    Fintype.card B = m → Odd m →
    Nat.Coprime n m → Nat.Coprime (n * m) 10 →
    (∀ g, g ∈ connectionSet A B → g⁻¹ ∈ connectionSet A B) ∧
      (1 : A × B × D10) ∉ connectionSet A B

def commutesWithAction {B X : Type*} [Group B] [MulAction B X]
    (p : Equiv.Perm X) : Prop :=
  ∀ (b : B) (x : X), p (b • x) = b • p x

def regularOrbit {B X : Type*} [SMul B X] (x : X) : Prop :=
  Function.Injective (fun b : B => b • x)

def twoRegularOrbits {B X : Type*} [SMul B X] : Prop :=
  ∃ x₀ x₁ : X,
    regularOrbit (B := B) x₀ ∧ regularOrbit (B := B) x₁ ∧
      Disjoint (MulAction.orbit B x₀) (MulAction.orbit B x₁) ∧
      MulAction.orbit B x₀ ∪ MulAction.orbit B x₁ = Set.univ

def doubleOrbitAlignment {B X : Type*} [Group B] [SMul B X]
    (e : X ≃ B × Fin 2) : Prop :=
  ∀ (b g : B) (i : Fin 2),
    e (b • e.symm (g, i)) = (b * g, i)

def generatedByAction {B X : Type*} [Group B] [MulAction B X]
    (u : Equiv.Perm X) : Subgroup (Equiv.Perm X) :=
  Subgroup.closure (Set.range (MulAction.toPermHom B X) ∪ {u})

def permutationSubgroupRegular {X : Type*}
    (H : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ x : X, Function.Bijective (fun h : H => h.1 x)

def uniqueInvolution {X : Type*} (H : Subgroup (Equiv.Perm X))
    (u : Equiv.Perm X) : Prop :=
  ∀ h : Equiv.Perm X, h ∈ H → h ^ (2 : ℕ) = 1 → h = 1 ∨ h = u

/-- An explicit two-orbit coordinate form for the centralizer and its
involution consequences. -/
def claim_30693 : Prop :=
  ∀ (B X : Type*) [Group B] [Fintype B] [Fintype X]
    [MulAction B X] (m : ℕ),
    Odd m → Fintype.card B = m → Fintype.card X = 2 * m →
    (∀ (b : B) (x : X), b • x = x → b = 1) →
    twoRegularOrbits (B := B) (X := X) →
    ∃ e : X ≃ B × Fin 2,
      doubleOrbitAlignment (B := B) (X := X) e ∧
        (∀ p : Equiv.Perm X,
          commutesWithAction (B := B) (X := X) p ↔
            ∃ σ : Equiv.Perm (Fin 2), ∃ k : Fin 2 → B,
              ∀ (g : B) (i : Fin 2),
                e (p (e.symm (g, i))) = (g * k i, σ i)) ∧
        Nat.card {p : Equiv.Perm X //
          commutesWithAction (B := B) (X := X) p} = 2 * m ^ 2 ∧
        (∀ (u : Equiv.Perm X),
          commutesWithAction (B := B) (X := X) u → u ≠ 1 → u ^ (2 : ℕ) = 1 →
            (∀ (g : B) (i : Fin 2),
              (e (u (e.symm (g, i)))).2 = (Equiv.swap (0 : Fin 2) 1) i) ∧
            let H := generatedByAction (B := B) (X := X) u
            u ∈ H ∧ permutationSubgroupRegular H ∧
              Nonempty (H ≃* B × Equiv.Perm (Fin 2)) ∧
              uniqueInvolution H u)

end MathlibPlus.Open.ResearchFormalization.BatchR1258
