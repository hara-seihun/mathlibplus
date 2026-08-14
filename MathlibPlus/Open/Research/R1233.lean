import Mathlib

namespace MathlibPlus.Open.Research.R1233

noncomputable section

variable {M L : Type*} [Group M] [Group L] [Finite M] [Finite L]

def MapsIsomorphicallyOnto (φ : M →* L) (A : Subgroup M) : Prop :=
  Function.Bijective (fun a : A => φ (a : M))

def IsComplementOf (K A : Subgroup M) : Prop :=
  (∀ m : M, ∃ k : K, ∃ a : A, (k : M) * (a : M) = m) ∧ K ⊓ A = ⊥

def IsNormalSubgroup (K : Subgroup M) : Prop :=
  ∀ m : M, ∀ k : M, k ∈ K → m * k * m⁻¹ ∈ K

def IsPSubgroup (p : Nat) (K : Subgroup M) : Prop :=
  ∃ exponent : Nat, Nat.card K = p ^ exponent

def IsHallSubgroup (K : Subgroup M) : Prop :=
  Nat.Coprime (Nat.card K) (Nat.card M / Nat.card K)

def ConjugateSubgroupEquality (B A : Subgroup M) (k : M) : Prop :=
  ∀ x : M, x ∈ A ↔ k * x * k⁻¹ ∈ B

def claim30409 : Prop :=
  ∀ (φ : M →* L) (A B : Subgroup M),
    MapsIsomorphicallyOnto φ A → MapsIsomorphicallyOnto φ B →
      IsComplementOf φ.ker A ∧ IsComplementOf φ.ker B

end

noncomputable section

variable {M L H : Type*} [Group M] [Group L] [Group H] [Finite M] [Finite L] [Finite H]

def claim30410 : Prop :=
  ∀ (p : Nat) (φ : M →* L) (K A B : Subgroup M),
    Nat.Prime p →
    K = φ.ker →
    IsNormalSubgroup K →
    IsPSubgroup p K →
    Nat.card L = Nat.card H →
    ¬ p ∣ Nat.card H →
    IsComplementOf K A → IsComplementOf K B →
    (IsNormalSubgroup K ∧ IsHallSubgroup K) ∧
      ∃ k : K, ConjugateSubgroupEquality B A (k : M)

end

end MathlibPlus.Open.Research.R1233
