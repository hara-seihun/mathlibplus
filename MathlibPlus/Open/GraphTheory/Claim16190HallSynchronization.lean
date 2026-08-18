import MathlibPlus.Open.GraphTheory.Claim16172CayleyFiber

namespace MathlibPlus.Open.GraphTheory

noncomputable section
open Classical

/-- Square-freeness of the cyclic Hall order. -/
def squareFree16190 (m : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → ¬ q ^ 2 ∣ m

/-- The orbit relation of a permutation subgroup. -/
def subgroupOrbitRelation16190 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (x y : Ω) : Prop :=
  ∃ p : P, p.1 x = y

/-- The orbit set of a point under a permutation subgroup. -/
def subgroupOrbitSet16190 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | subgroupOrbitRelation16190 P x y}

/-- The orbit relation of a subgroup after a permutation conjugation. -/
def conjugatedSubgroupOrbitRelation16190 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω)
    (x y : Ω) : Prop :=
  ∃ p : P, (g * p.1 * g⁻¹) x = y

/-- Membership in the conjugate of a subgroup, written without constructing a
subgroup-valued conjugation. -/
def conjugatedSubgroupMembership16190 {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω)
    (x : Equiv.Perm Ω) : Prop :=
  ∃ p : P, x = g * p.1 * g⁻¹

/-- Cyclic Sylow-coordinate space, with one coordinate for every prime divisor
of `m`. -/
def primeDivisorIndex16190 (m : ℕ) :=
  {p : ℕ // Nat.Prime p ∧ p ∣ m}

abbrev cartesianSylowSpace16190 (m : ℕ) :=
  ∀ p : primeDivisorIndex16190 m, Fin p.1

/-- A permutation of `Fin p` is one `p`-cycle. -/
def isPCycle16190 (p : ℕ) (σ : Equiv.Perm (Fin p)) : Prop :=
  ∀ x : Fin p,
    Set.range (fun k : Fin p => (σ ^ k.1) x) = Set.univ

/-- Repetition of one local `p`-cycle across all other Sylow coordinates. -/
def repeatedSylowAction16190 {Ω : Type*}
    (m p : ℕ) (hp : Nat.Prime p) (hpm : p ∣ m)
    (cart : Ω → cartesianSylowSpace16190 m) (B : Set Ω)
    (Q : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω) : Prop :=
  ∃ d : Q,
    (∀ q : Q, ∃ k : Fin p, q.1 = d.1 ^ k.1) ∧
      ∃ σ : Equiv.Perm (Fin p),
        isPCycle16190 p σ ∧
          ∀ x : Ω, x ∈ B →
            (g * d.1 * g⁻¹) x ∈ B ∧
              cart ((g * d.1 * g⁻¹) x) =
                Function.update (cart x) ⟨p, hp, hpm⟩
                  (σ ((cart x) ⟨p, hp, hpm⟩))

/-- A cyclic order-`m` action which is regular on each of its orbits. -/
def regularCyclicHallAction16190 {Ω : Type*}
    (m : ℕ) (C : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nat.card C = m ∧
    Nonempty (Multiplicative (ZMod m) ≃* C) ∧
      ∀ x : Ω, Set.ncard (subgroupOrbitSet16190 C x) = m

/-- The fibre of a block coordinate. -/
def hallBlock16190 {Ω B : Type*} (coord : Ω ≃ B × ZMod m)
    (h : B) : Set Ω :=
  {x | (coord x).1 = h}

/-- Equality of two cyclic subgroup actions on one block, written pointwise
in both directions. -/
def sameActionOnBlock16190 {Ω : Type*}
    (L M : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω)
    (B : Set Ω) : Prop :=
  ∀ x ∈ B,
    (∀ l : L, ∃ d : M, l.1 x = (g * d.1 * g⁻¹) x) ∧
      (∀ d : M, ∃ l : L, (g * d.1 * g⁻¹) x = l.1 x)

/-- Hall-block equality after the two successive conjugations. -/
def simultaneousHallAlignment16190 {Ω B : Type*} [Fintype Ω]
    (m : ℕ) (C D : Subgroup (Equiv.Perm Ω))
    (coord : Ω ≃ B × ZMod m) (g : Equiv.Perm Ω) : Prop :=
  (∀ h : B, ∃ x : Ω,
    hallBlock16190 coord h = subgroupOrbitSet16190 C x ∧
      hallBlock16190 coord h =
        {y | conjugatedSubgroupOrbitRelation16190 D g x y}) ∧
  (∀ d : ℕ, d ∣ m →
    ∀ L : Subgroup (Equiv.Perm Ω), L ≤ C → Nat.card L = d →
      ∃ M : Subgroup (Equiv.Perm Ω), M ≤ D ∧ Nat.card M = d ∧
        ∀ h : B,
          sameActionOnBlock16190 L M g (hallBlock16190 coord h))

/-- The normal Hall-block condition supplied by the generated regular copies. -/
def normalHallBlocks16190 {Ω B : Type*}
    (K : Subgroup (Equiv.Perm Ω)) (coord : Ω ≃ B × ZMod m) : Prop :=
  ∀ k : K, ∀ h : B,
    ∃ h' : B, k.1 '' hallBlock16190 coord h = hallBlock16190 coord h'

/-- Conjugation of full regular copies after the Hall alignment. -/
def fullCopyConjugator16190 {Ω : Type*}
    (R T : Subgroup (Equiv.Perm Ω)) (g φ : Equiv.Perm Ω) : Prop :=
  ∀ x : Equiv.Perm Ω,
    conjugatedSubgroupMembership16190 T g x ↔
      ∃ y : Equiv.Perm Ω, y ∈ R ∧ x = φ * y * φ⁻¹

/-- Cartesian repetition and simultaneous Hall synchronization for regular
cyclic Hall copies.  The first conclusion is the repeated Sylow cycle in
Cartesian coordinates; the second is equality of cyclic Hall actions on each
Hall block; the last clause is the affine skew form of every full-copy
conjugator. -/
def cartesian_repetition_simultaneous_hall_synchronization : Prop :=
  ∀ (m : ℕ), 1 < m → squareFree16190 m →
    ∀ (Ω : Type*) [Fintype Ω]
      (R T C D : Subgroup (Equiv.Perm Ω)),
      regularPermutationGroup16172 R →
      regularPermutationGroup16172 T →
      C ≤ R → D ≤ T →
      regularCyclicHallAction16190 m C →
      regularCyclicHallAction16190 m D →
      (∀ p : ℕ, Nat.Prime p → p ∣ m →
        ∃ P : Subgroup (Equiv.Perm Ω), ∃ Q : Subgroup (Equiv.Perm Ω),
          P ≤ C ∧ Q ≤ D ∧ Nat.card P = p ∧ Nat.card Q = p ∧
            ∀ x y : Ω,
              subgroupOrbitRelation16190 P x y ↔
                subgroupOrbitRelation16190 Q x y) →
      ∃ (B : Type*) (cart : Ω → cartesianSylowSpace16190 m)
        (hall : Ω ≃ B × ZMod m) (g₀ g₁ : Equiv.Perm Ω),
        (∀ h : B,
          Function.Bijective
            (fun x : {y : Ω // y ∈ hallBlock16190 hall h} => cart x.1)) ∧
        g₀ ∈ generatedPairGroup16172 R T ∧
          g₁ ∈ generatedPairGroup16172 R T ∧
          (∀ (p : ℕ) (hp : Nat.Prime p) (hpm : p ∣ m),
            ∀ P : Subgroup (Equiv.Perm Ω), P ≤ C → Nat.card P = p →
              ∃ Q : Subgroup (Equiv.Perm Ω), Q ≤ D ∧ Nat.card Q = p ∧
                (∀ x y : Ω,
                  subgroupOrbitRelation16190 P x y ↔
                    conjugatedSubgroupOrbitRelation16190 Q g₀ x y) ∧
                (∀ h : B,
                  repeatedSylowAction16190 m p hp hpm cart
                    (hallBlock16190 hall h) Q g₀)) ∧
          simultaneousHallAlignment16190 m C D hall (g₁ * g₀) ∧
          normalHallBlocks16190 (m := m)
            (generatedPairGroup16172 R T) hall ∧
          (∀ φ : Equiv.Perm Ω,
            fullCopyConjugator16190 R T (g₁ * g₀) φ →
              ∃ f : B ≃ B, ∃ u : B → (ZMod m)ˣ, ∃ t : B → ZMod m,
                ∀ h : B, ∀ z : ZMod m,
                  hall (φ (hall.symm (h, z))) =
                    (f h, (u h : ZMod m) * z + t h))

end

end MathlibPlus.Open.GraphTheory
