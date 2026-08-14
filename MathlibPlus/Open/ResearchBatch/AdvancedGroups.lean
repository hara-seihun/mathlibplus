import Mathlib

noncomputable section
open Classical
attribute [local instance] Classical.propDecidable

namespace MathlibPlus.Open.ResearchBatch.AdvancedGroups

/-- The affine permutation with translation part `v` and linear part `c`. -/
def affineMap {K W : Type*} [Semiring K] [AddCommGroup W] [Module K W]
    (v : W) (c : W ≃ₗ[K] W) : Equiv.Perm W :=
  c.toEquiv.trans (Equiv.addLeft v)

def affineContainedIn {K W : Type*} [Semiring K] [AddCommGroup W] [Module K W]
    (C : Subgroup (W ≃ₗ[K] W)) (Γ : Subgroup (Equiv.Perm W)) : Prop :=
  ∀ γ : Equiv.Perm W, γ ∈ Γ →
    ∃ v : W, ∃ c : W ≃ₗ[K] W, c ∈ C ∧ γ = affineMap v c

def affineTranslationCore {K W : Type*} [Semiring K] [AddCommGroup W] [Module K W]
    (Γ : Subgroup (Equiv.Perm W)) : Set W :=
  {v | affineMap v (1 : W ≃ₗ[K] W) ∈ Γ}

def affineOrbit {W : Type*} [AddCommGroup W]
    (Γ : Subgroup (Equiv.Perm W)) (x : W) : Set W :=
  {y | ∃ γ : Γ, γ.1 x = y}

def commonTranslationStabilizer {K W : Type*} [Semiring K] [AddCommGroup W] [Module K W]
    (Γ : Subgroup (Equiv.Perm W)) : Set W :=
  {v | ∀ x y, y ∈ affineOrbit Γ x ↔
      affineMap v (1 : W ≃ₗ[K] W) y ∈ affineOrbit Γ x}

/-- The common translation stabilizer of all affine orbits is the translation core. -/
def claim39440 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)] (W : Type*) [Fintype W] [AddCommGroup W]
    [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (C : Subgroup (W ≃ₗ[ZMod p] W)) [Fintype C]
    (Γ : Subgroup (Equiv.Perm W)),
    Nat.Prime p → ¬ p ∣ Fintype.card C →
      affineContainedIn (K := ZMod p) (W := W) C Γ →
      commonTranslationStabilizer (K := ZMod p) (W := W) Γ =
        affineTranslationCore (K := ZMod p) (W := W) Γ

/-- The additive group `C_p² × C_q²` used by the two-closure statements. -/
abbrev Cp2Cq2 (p q : ℕ) := (ZMod p × ZMod p) × (ZMod q × ZMod q)

def rightTranslation {G : Type*} [AddGroup G] (a : G) : Equiv.Perm G :=
  Equiv.addRight a

def rightRegularGroup (G : Type*) [Fintype G] [AddCommGroup G] :=
  Subgroup.closure (Set.range (rightTranslation (G := G)))

/-- The diagonal orbitals and the exact permutation two-closure. -/
def groupOrbital {G : Type*}
    (X : Subgroup (Equiv.Perm G)) (a b : G) : Set (G × G) :=
  {p | ∃ x : X, x.1 a = p.1 ∧ x.1 b = p.2}

def preservesAllOrbitals {G : Type*}
    (X : Subgroup (Equiv.Perm G)) (f : Equiv.Perm G) : Prop :=
  ∀ a b, ∀ p, p ∈ groupOrbital X a b ↔
    (f p.1, f p.2) ∈ groupOrbital X a b

def isTwoClosed {G : Type*} (X : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ f, preservesAllOrbitals X f → f ∈ X

def regularPermutationCopy {G : Type*} [AddGroup G]
    (K : Subgroup (Equiv.Perm G)) : Prop :=
  Nonempty (Multiplicative G ≃* K) ∧
    ∀ x y : G, ∃! k : K, k.1 x = y

def conjugateSubgroupsIn {G : Type*}
    (X : Subgroup (Equiv.Perm G))
    (K L : Subgroup (Equiv.Perm G)) : Prop :=
  ∃ x : X, ∀ l : Equiv.Perm G, l ∈ L ↔
    ∃ k : Equiv.Perm G, k ∈ K ∧ l = x.1 * k * x.1⁻¹

/-- The extracted `CI^(2)` theorem for `C_p² × C_q²`. -/
def claim39562 : Prop :=
  ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Prime p → Nat.Prime q → p ≠ q →
    ∀ (X : Subgroup (Equiv.Perm (Cp2Cq2 p q))),
      isTwoClosed X →
      rightRegularGroup (Cp2Cq2 p q) ≤ X →
      ∀ K L : Subgroup (Equiv.Perm (Cp2Cq2 p q)),
        K ≤ X → L ≤ X → regularPermutationCopy K → regularPermutationCopy L →
          conjugateSubgroupsIn X K L

/-- A finite tuple of directed binary Cayley relations on the same group. -/
def tupleCayleyRelation {G : Type*} [AddGroup G]
    (S : Finset G) (x y : G) : Prop := y - x ∈ S

def tupleAutomorphism {G ι : Type*} [AddGroup G] [Fintype ι]
    (S : ι → Finset G) (e : Equiv.Perm G) : Prop :=
  ∀ i x y, tupleCayleyRelation (S i) x y ↔
    tupleCayleyRelation (S i) (e x) (e y)

def tupleCI {G ι : Type*} [AddGroup G] [Fintype ι]
    (S : ι → Finset G) : Prop :=
  ∀ K L : Subgroup (Equiv.Perm G),
    (∀ k : Equiv.Perm G, k ∈ K → tupleAutomorphism S k) →
    (∀ l : Equiv.Perm G, l ∈ L → tupleAutomorphism S l) →
    regularPermutationCopy K → regularPermutationCopy L →
    ∃ e : Equiv.Perm G, tupleAutomorphism S e ∧
      (∀ l : Equiv.Perm G, l ∈ L ↔
        ∃ k : Equiv.Perm G, k ∈ K ∧ l = e * k * e⁻¹)

/-- Finite tuples, and hence directed and undirected Cayley graphs, are CI. -/
def claim39563 : Prop :=
  ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Prime p → Nat.Prime q → p ≠ q →
    ∀ (ι : Type*) [Fintype ι]
      (S : ι → Finset (Cp2Cq2 p q)), tupleCI S

end MathlibPlus.Open.ResearchBatch.AdvancedGroups
