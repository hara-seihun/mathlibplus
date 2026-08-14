import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CycleClaims

universe u

/-- The conjugate convention used by the admitted cycle claims: `g^h = h⁻¹ g h`. -/
def conjugate {G : Type u} [Group G] (g h : G) : G := h⁻¹ * g * h

/-- A cyclic permutation whose orbit on a `q`-point carrier is all of that carrier. -/
def RegularCycle (q : ℕ) {α : Type u} [Fintype α]
    (ρ : Equiv.Perm α) : Prop :=
  Fintype.card α = q ∧
    ∀ x y : α, ∃ k : Fin q, (ρ ^ (k : ℕ)) x = y

def NormalIn {G : Type u} [Group G] (B A : Subgroup G) : Prop :=
  B ≤ A ∧ ∀ a, a ∈ A → ∀ b, b ∈ B → a * b * a⁻¹ ∈ B

/-- A carrier-free spelling of cyclicity for a quotient, used to avoid hiding
its generator in an unelaborated quotient notation. -/
def CyclicQuotient {G : Type u} [Group G] (A B : Subgroup G) : Prop :=
  B ≤ A ∧ ∃ g, g ∈ A ∧ ∀ a, a ∈ A → ∃ n : ℤ, a * (g ^ n)⁻¹ ∈ B

def claim_38750 : Prop :=
  ∀ (q : ℕ) {α : Type u} [Fintype α] (ρ : Equiv.Perm α),
    Nat.Prime q → 5 ≤ q → RegularCycle q ρ →
    ∀ σ : Equiv.Perm α,
      let ρσ := conjugate ρ σ
      let δ := ρ⁻¹ * ρσ
      let A : Subgroup (Equiv.Perm α) :=
        Subgroup.closure ({ρ, ρσ} : Set (Equiv.Perm α))
      let B : Subgroup (Equiv.Perm α) :=
        Subgroup.closure
          (Set.range (fun k : Fin q => conjugate δ (ρ ^ (k : ℕ))))
      NormalIn B A ∧ ρσ = ρ * δ ∧ CyclicQuotient A B

/-- The affine permutations of the standard one-dimensional `q`-point field. -/
def affineLinePermutations (q : ℕ) : Set (Equiv.Perm (ZMod q)) :=
  {σ | ∃ a : (ZMod q)ˣ, ∃ b : ZMod q,
    ∀ x : ZMod q, σ x = (a : ZMod q) * x + b}

def claim_38755 : Prop :=
  ∀ (q : ℕ), (hq : Nat.Prime q) → 5 ≤ q →
    letI : Fact (Nat.Prime q) := ⟨hq⟩
    let ρ : Equiv.Perm (ZMod q) := Equiv.addRight 1
    let C : Subgroup (Equiv.Perm (ZMod q)) :=
      Subgroup.closure ({ρ} : Set (Equiv.Perm (ZMod q)))
    let N : Subgroup (Equiv.Perm (ZMod q)) := Subgroup.normalizer (C : Set _)
    letI : Fintype N := Fintype.ofFinite N
    (N : Set (Equiv.Perm (ZMod q))) = affineLinePermutations q ∧
      Fintype.card N = q * (q - 1) ∧
      ∀ σ : Equiv.Perm (ZMod q),
        (conjugate ρ σ ∈ C ↔ σ ∈ N)

end MathlibPlus.Open.ResearchFormalization.CycleClaims
