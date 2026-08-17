import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2888Claim47377

noncomputable section

/-- Conjugation in the convention `S^f = f⁻¹ S f`. -/
def conjugateSubgroupBy {E : Type*} [Group E]
    (f : E) (S : Subgroup E) : Subgroup E :=
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj f⁻¹)) S

/-- The subgroup product is an internal direct product. -/
def internalDirectProduct {E : Type*} [Group E]
    (P U R : Subgroup E) : Prop :=
  P ≤ R ∧ U ≤ R ∧ P ⊓ U = ⊥ ∧ P ⊔ U = R ∧
    (∀ p : P, ∀ u : U, (p : E) * (u : E) = (u : E) * (p : E))

/-- A specified copy acts regularly on the actual permutation domain. -/
def regularPermutationCopyIn
    {A H Ω : Type*} [Group A] [Group H]
    (M : Subgroup (Equiv.Perm Ω))
    (R : Subgroup M) (e : A × H ≃* R) : Prop :=
  ∀ x y : Ω, ∃! h : A × H,
    ((((e h : R) : M) : Equiv.Perm Ω)) x = y

/-- Characteristicity for a subgroup of the actual generated group. -/
def characteristicSubgroup {M : Type*} [Group M]
    (R P : Subgroup M) : Prop :=
  P ≤ R ∧
    ∀ φ : R ≃* R, ∀ r : R,
      (r : M) ∈ P ↔ (φ r : M) ∈ P

/-- Hall-π and characteristic Hall-π conditions on the actual carrier. -/
def characteristicHallPi {M : Type*} [Group M]
    (R P : Subgroup M) (n : ℕ) : Prop :=
  characteristicSubgroup R P ∧
    P ≤ R ∧
      (∀ p : ℕ, Nat.Prime p →
        (p ∣ Nat.card P ↔ p ∣ Nat.card R ∧ p ∣ n)) ∧
      Nat.Coprime (Nat.card P) (Nat.card R / Nat.card P)

def characteristicHallPiPrime {M : Type*} [Group M]
    (R U : Subgroup M) (n : ℕ) : Prop :=
  characteristicSubgroup R U ∧
    U ≤ R ∧
      (∀ p : ℕ, Nat.Prime p →
        (p ∣ Nat.card U ↔ p ∣ Nat.card R ∧ ¬p ∣ n)) ∧
      Nat.Coprime (Nat.card U) (Nat.card R / Nat.card U)

/-- The actual orbit partition of a subgroup of the generated permutation group. -/
def subgroupOrbitPartitionIn
    {Ω : Type*} (M : Subgroup (Equiv.Perm Ω))
    (P : Subgroup M) : Set (Set Ω) :=
  Set.range (fun x : Ω =>
    {y | ∃ p : P, (((p : P) : M) : Equiv.Perm Ω) x = y})

/-- A genuine induced permutation on the named block system. -/
def inducesBlockPermutation {Ω : Type*}
    (B : Set (Set Ω)) (f : Equiv.Perm Ω) (q : Equiv.Perm B) : Prop :=
  ∀ C : B, ((q C : B) : Set Ω) = f '' (C : Set Ω)

/-- Exact block image of a subgroup, with existence and uniqueness of every
induced action and no free quotient callback. -/
def actualBlockCopyImage {Ω : Type*}
    (M : Subgroup (Equiv.Perm Ω))
    (R : Subgroup M) (B : Set (Set Ω))
    (L : Subgroup (Equiv.Perm B)) : Prop :=
  (∀ r : R, ∃! q : Equiv.Perm B,
    inducesBlockPermutation B
      ((((r : R) : M) : Equiv.Perm Ω)) q) ∧
    (∀ q : Equiv.Perm B, q ∈ L ↔
      ∃ r : R, inducesBlockPermutation B
        ((((r : R) : M) : Equiv.Perm Ω)) q)

/-- Exact image of the whole generated permutation group on the blocks. -/
def actualBlockImage {Ω : Type*}
    (M : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω))
    (L : Subgroup (Equiv.Perm B)) : Prop :=
  (∀ m : M, ∃! q : Equiv.Perm B,
    inducesBlockPermutation B (m : Equiv.Perm Ω) q) ∧
    (∀ q : Equiv.Perm B, q ∈ L ↔
      ∃ m : M, inducesBlockPermutation B (m : Equiv.Perm Ω) q)

/-- The exact block-action kernel inside the actual generated group. -/
def exactBlockKernel {Ω : Type*}
    (M : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω))
    (K : Subgroup M) : Prop :=
  ∀ k : M, k ∈ K ↔
    ∀ C : B, (k : Equiv.Perm Ω) '' (C : Set Ω) = (C : Set Ω)

/-- The additive kernel is identified with the actual block kernel. -/
def identifiesActualKernel
    {K Ω : Type*} [AddCommGroup K]
    (M : Subgroup (Equiv.Perm Ω)) (K₀ : Subgroup M)
    (ι : Multiplicative K →* M) : Prop :=
  Function.Injective ι ∧
    (∀ x : K, ι (Multiplicative.ofAdd x) ∈ K₀) ∧
    (∀ k : K₀, ∃ x : K, ι (Multiplicative.ofAdd x) = k)

/-- A genuine additive one-cocycle for the displayed group action. -/
def additiveOneCocycle {K L : Type*} [AddCommGroup K]
    [Group L] [DistribMulAction L K] (d : L → K) : Prop :=
  ∀ l m : L, d (l * m) = d l + l • d m

/-- The averaged coboundary witness. -/
def averagedCoboundary {K L : Type*} [AddCommGroup K]
    [Group L] [Fintype L] [DistribMulAction L K]
    (d : L → K) (a : K) : Prop :=
  (Nat.card L) • a = ∑ l : L, d l ∧
    ∀ l : L, d l = a - l • a

/-- An actual group extension carries the kernel as the exact kernel of its
quotient map. -/
def exactFiniteExtensionKernel
    {K M L : Type*} [AddCommGroup K] [Group M] [Group L]
    (ι : Multiplicative K →* M) (π : M →* L) : Prop :=
  Function.Injective ι ∧
    (∀ x : K, π (ι (Multiplicative.ofAdd x)) = 1) ∧
    (∀ m : M, π m = 1 →
      ∃ x : K, ι (Multiplicative.ofAdd x) = m)

/-- The section/cocycle carrier used for the complement argument. -/
def sectionedCocycleExtension
    {K M L : Type*} [AddCommGroup K] [Group M] [Group L]
    [DistribMulAction L K]
    (ι : Multiplicative K →* M) (π : M →* L)
    (s sV : L →* M) (d : L → K) : Prop :=
  exactFiniteExtensionKernel ι π ∧
    (∀ l : L, π (s l) = l) ∧
    (∀ l : L, π (sV l) = l) ∧
    (∀ l : L, ∀ x : K,
      ι (Multiplicative.ofAdd (l • x)) =
        s l * ι (Multiplicative.ofAdd x) * (s l)⁻¹) ∧
    (∀ l : L,
      sV l = ι (Multiplicative.ofAdd (d l)) * s l) ∧
    additiveOneCocycle d

/-- Claim 47377: for the exact aligned Hall extension, the averaging element
conjugates the Hall complement and therefore the full regular copy. -/
def claim47377 : Prop :=
  ∀ (A H Ω : Type*) [CommGroup A] [Group H]
    [Fintype A] [Fintype H] [Fintype Ω]
    (M : Subgroup (Equiv.Perm Ω))
    (R T P : Subgroup M) (B : Set (Set Ω))
    (L : Subgroup (Equiv.Perm B))
    (eR : A × H ≃* R) (eT : A × H ≃* T)
    (K : Type*) [AddCommGroup K] [Fintype K]
    [Fintype L] [DistribMulAction L K]
    (ι : Multiplicative K →* M) (π : M →* L)
    (K₀ : Subgroup M) (s sV : L →* M) (d : L → K) (a : K),
    Nat.Coprime (Nat.card L) (Nat.card K) →
    regularPermutationCopyIn M R eR →
    regularPermutationCopyIn M T eT →
    characteristicHallPi R P (Nat.card A) →
    characteristicHallPi T P (Nat.card A) →
    subgroupOrbitPartitionIn M P = B →
    actualBlockCopyImage M R B L →
    actualBlockCopyImage M T B L →
    actualBlockImage M B L →
    (∀ m : M, inducesBlockPermutation B (m : Equiv.Perm Ω) (π m : L)) →
    exactBlockKernel M B K₀ →
    identifiesActualKernel M K₀ ι →
    exactFiniteExtensionKernel ι π →
    sectionedCocycleExtension ι π s sV d →
    Subgroup.closure ((R : Set M) ∪ (T : Set M)) = ⊤ →
    characteristicHallPiPrime R (MonoidHom.range s) (Nat.card A) →
    characteristicHallPiPrime T (MonoidHom.range sV) (Nat.card A) →
    internalDirectProduct P (MonoidHom.range s) R →
    internalDirectProduct P (MonoidHom.range sV) T →
    (∀ p : P, ∀ x : K,
      (p : M) * ι (Multiplicative.ofAdd x) =
        ι (Multiplicative.ofAdd x) * (p : M)) →
    averagedCoboundary d a →
      (∀ l : L,
        (ι (Multiplicative.ofAdd (-a)))⁻¹ * s l *
            ι (Multiplicative.ofAdd (-a)) = sV l) ∧
      conjugateSubgroupBy (ι (Multiplicative.ofAdd (-a)))
          (MonoidHom.range s) = MonoidHom.range sV ∧
      conjugateSubgroupBy (ι (Multiplicative.ofAdd (-a))) R =
          P ⊔ MonoidHom.range sV ∧
      P ⊔ MonoidHom.range sV = T ∧
      conjugateSubgroupBy (ι (Multiplicative.ofAdd (-a))) R = T

end
end MathlibPlus.Open.ResearchFormalization.R2888Claim47377
