import Mathlib

namespace MathlibPlus.Open.GroupTheory.Batch

/-- The primes occurring in a finite cardinality. -/
def primeDivisors (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ p ∣ n)

/-- All prime divisors of a finite group have been recorded in `π`. -/
def PrimeDivisorsIn (n : ℕ) (π : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ π

/-- Normality written without relying on a particular normal-subgroup API. -/
def NormalSubgroup {R : Type*} [Group R] (H : Subgroup R) : Prop :=
  ∀ (g x : R), x ∈ H → g * x * g⁻¹ ∈ H

/-- A normal `π`-subgroup. -/
def NormalPiSubgroup {R : Type*} [Group R] [Fintype R]
    (H : Subgroup R) (π : Finset ℕ) : Prop :=
  NormalSubgroup H ∧ PrimeDivisorsIn (Nat.card H) π

/-- The largest normal `π`-subgroup, i.e. the semantic content of `O_π(R)`. -/
def IsPiCore {R : Type*} [Group R] [Fintype R]
    (H : Subgroup R) (π : Finset ℕ) : Prop :=
  NormalPiSubgroup H π ∧
    ∀ K : Subgroup R, NormalPiSubgroup K π → K ≤ H

/-- The Hall condition used for a finite group and its prime set. -/
def IsHallPi {R : Type*} [Group R] [Fintype R]
    (H : Subgroup R) (π : Finset ℕ) : Prop :=
  Nat.card H ∣ Fintype.card R ∧
    PrimeDivisorsIn (Nat.card H) π ∧
    (∀ p : ℕ, Nat.Prime p →
      p ∣ (Fintype.card R / Nat.card H) → p ∉ π)

/-- The subgroup supported in one coordinate of a finite direct product. -/
def coordinateSubgroup {ι : Type*} [DecidableEq ι]
    (G : ι → Type*) [∀ i, Group (G i)] (i : ι) : Subgroup (∀ j, G j) where
  carrier := {x | ∀ j, j ≠ i → x j = 1}
  one_mem' := by
    intro j hj
    simp
  mul_mem' := by
    intro x y hx hy j hji
    simp [hx j hji, hy j hji]
  inv_mem' := by
    intro x hx j hji
    simp [hx j hji]

/-- Pulling a coordinate subgroup back through the selected product isomorphism. -/
def hallFactor {R : Type*} [Group R]
    {ι : Type*} [DecidableEq ι] (G : ι → Type*) [∀ i, Group (G i)]
    (e : R ≃* (∀ i, G i)) (i : ι) : Subgroup R :=
  (coordinateSubgroup G i).comap e.toMonoidHom

/-- Characteristicity of a subgroup. -/
def CharacteristicSubgroup {R : Type*} [Group R]
    (H : Subgroup R) : Prop :=
  ∀ φ : R ≃* R, H.map φ.toMonoidHom = H

/-- The coordinate factors generate the whole ambient group. -/
def CoordinateProductIsWhole {R : Type*} [Group R]
    {ι : Type*} (H : ι → Subgroup R) : Prop :=
  (⨆ i, H i) = ⊤

/-- Transitivity of a finite permutation subgroup. -/
def PermutationSubgroupTransitive {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃ p : P, p.1 x = y

/-- The product of two commuting permutation subgroups is transitive. -/
def CommutingProductTransitive {Ω : Type*}
    (P Q : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃ p : P, ∃ q : Q, (p.1 * q.1) x = y

/-- Pairwise commutation of two permutation subgroups. -/
def PermutationSubgroupsCommute {Ω : Type*}
    (P Q : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ p : P, ∀ q : Q, p.1 * q.1 = q.1 * p.1

/-- Claim 31460: in a coprime direct product, the characteristic Hall factors are
exactly the coordinate factors and form the direct product. -/
def claim31460 : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [Group R] [Fintype R]
    (G : ι → Type*) [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (e : R ≃* (∀ i, G i)),
    (∀ i j : ι, i ≠ j →
      Nat.Coprime (Fintype.card (G i)) (Fintype.card (G j))) →
    (∀ i : ι,
      IsPiCore (hallFactor G e i) (primeDivisors (Fintype.card (G i))) ∧
      IsHallPi (hallFactor G e i) (primeDivisors (Fintype.card (G i))) ∧
      CharacteristicSubgroup (hallFactor G e i)) ∧
    (∀ i j : ι, i ≠ j →
      ∀ x y : R, x ∈ hallFactor G e i → y ∈ hallFactor G e j → x * y = y * x) ∧
    CoordinateProductIsWhole (hallFactor G e)

/-- Claim 31461: the coprime orbit-count argument for a coordinate projection.
The hypothesis that the coordinate degree is a `π`-number is made explicit,
as it is the premise used by the stated divisibility argument. -/
def claim31461 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (π : Finset ℕ) (P Q : Subgroup (Equiv.Perm Ω)),
    CommutingProductTransitive P Q →
    PermutationSubgroupsCommute P Q →
    PrimeDivisorsIn (Nat.card P) π →
    (∀ p : ℕ, Nat.Prime p → p ∣ Nat.card Q → p ∉ π) →
    PrimeDivisorsIn (Fintype.card Ω) π →
    PermutationSubgroupTransitive P

end MathlibPlus.Open.GroupTheory.Batch
