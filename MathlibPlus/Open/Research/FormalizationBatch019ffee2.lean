import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

abbrev Q4qCarrier (q : ℕ) := ZMod q × Fin 4

def q4qAction (q : ℕ) (i : Fin 4) (y : ZMod q) : ZMod q :=
  (-1 : ZMod q) ^ i.val * y

def q4qMul (q : ℕ) (h k : Q4qCarrier q) : Q4qCarrier q :=
  (h.1 + q4qAction q h.2 k.1, h.2 + k.2)

def q4qInv (q : ℕ) (h : Q4qCarrier q) : Q4qCarrier q :=
  (-q4qAction q h.2 h.1, -h.2)

abbrev Q4pqCarrier (p q : ℕ) := ZMod p × Q4qCarrier q

/-- The coordinate form of the normalized chart in Claim 40100. -/
def normalizedChart40100 (p q : ℕ) (ζ : (ZMod p)ˣ)
    (f : Q4pqCarrier p q → Q4pqCarrier p q) : Prop :=
  Nat.Prime p → Nat.Prime q → p ≠ q → 2 < p → 2 < q → q ∣ p - 1 →
    orderOf ζ = q →
  ∃ (r : Fin 4 → ZMod q) (u t : Fin 4 → ZMod q)
    (π : Fin 4 → Fin 4) (τ : Q4qCarrier q → ZMod p),
    (∀ i, u i ≠ 0) ∧ t 0 = 0 ∧ π 0 = 0 ∧ τ ⟨0, 0⟩ = 0 ∧
      (∃ i, r i ≠ 0) ∧
      (∀ x y i,
        f ⟨x, ⟨y, i⟩⟩ =
          ⟨((ζ ^ (r i * y).val : (ZMod p)ˣ) : ZMod p) * x + τ ⟨y, i⟩,
            ⟨u i * y + t i, π i⟩⟩)

def affineOnFourBlocks40113 (q : ℕ)
    (σ : Q4qCarrier q → Q4qCarrier q) : Prop :=
  ∃ (u t : Fin 4 → ZMod q) (π : Fin 4 → Fin 4),
    (∀ i, u i ≠ 0) ∧
      (∀ y i, σ ⟨y, i⟩ = ⟨u i * y + t i, π i⟩)

/-- The coordinate form of a normalized triangular affine map in Claim 40113. -/
def triangularAffineMap40113 (p q : ℕ)
    (f : Q4pqCarrier p q → Q4pqCarrier p q) : Prop :=
  Nat.Prime p → Nat.Prime q → p ≠ q → 2 < p → 2 < q →
  ∃ (scalar : Q4qCarrier q → (ZMod p)ˣ) (τ : Q4qCarrier q → ZMod p)
    (σ : Q4qCarrier q → Q4qCarrier q),
    (∀ x h,
      f ⟨x, h⟩ =
        ⟨((scalar h : (ZMod p)ˣ) : ZMod p) * x + τ h, σ h⟩) ∧
      affineOnFourBlocks40113 q σ

def sigma40102 (q : ℕ) (u t : Fin 4 → ZMod q) (π : Fin 4 → Fin 4)
    (h : Q4qCarrier q) : Q4qCarrier q :=
  (u h.2 * h.1 + t h.2, π h.2)

def chi40102 (p q : ℕ) (h : Q4qCarrier q) : (ZMod p)ˣ :=
  (-1 : (ZMod p)ˣ) ^ h.2.val

def lambda40102 (p q : ℕ) (ζ : (ZMod p)ˣ) (r : Fin 4 → ZMod q)
    (h : Q4qCarrier q) : (ZMod p)ˣ :=
  ζ ^ (r h.2 * h.1).val

def transformedScalar40102 (p q : ℕ) (ζ : (ZMod p)ˣ)
    (r u t : Fin 4 → ZMod q) (π : Fin 4 → Fin 4)
    (h : Q4qCarrier q) : (ZMod p)ˣ :=
  lambda40102 p q ζ r h * chi40102 p q h /
    chi40102 p q (sigma40102 q u t π h)

def scalarPeriod40102 (p q : ℕ) (ζ : (ZMod p)ˣ)
    (r u t : Fin 4 → ZMod q) (π : Fin 4 → Fin 4) : Set (Q4qCarrier q) :=
  {h | ∀ k, transformedScalar40102 p q ζ r u t π (q4qMul q h k) =
    transformedScalar40102 p q ζ r u t π k}

def q4qSubgroup40102 (q : ℕ) (K : Set (Q4qCarrier q)) : Prop :=
  (⟨0, 0⟩ : Q4qCarrier q) ∈ K ∧
    (∀ h k, h ∈ K → k ∈ K → q4qMul q h k ∈ K) ∧
    (∀ h, h ∈ K → q4qInv q h ∈ K)

/-- Claim 40102: the displayed scalar period is the subgroup stabilizing the
transformed scalar under left translation. -/
def claim40102 : Prop :=
  ∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p ≠ q → 2 < p → 2 < q →
    q ∣ p - 1 →
    ∀ (ζ : (ZMod p)ˣ) (r u t : Fin 4 → ZMod q) (π : Fin 4 → Fin 4),
      orderOf ζ = q →
      (∀ i, u i ≠ 0) →
      t 0 = 0 → π 0 = 0 →
      q4qSubgroup40102 q (scalarPeriod40102 p q ζ r u t π)

/-- Claim 40104: invariance of the scalar period on the characteristic layer
forces the exponent profile to vanish. -/
def claim40104 : Prop :=
  ∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p ≠ q → 2 < p → 2 < q →
    q ∣ p - 1 →
    ∀ (ζ : (ZMod p)ˣ) (r u t : Fin 4 → ZMod q) (π : Fin 4 → Fin 4),
      orderOf ζ = q →
      (∀ i, u i ≠ 0) →
      t 0 = 0 → π 0 = 0 →
      ((∀ s : ZMod q, (⟨s, 0⟩ : Q4qCarrier q) ∈
          scalarPeriod40102 p q ζ r u t π) →
        ((∀ i s y,
            ζ ^ (r i * (s + y)).val = ζ ^ (r i * y).val) ∧
          (∀ i, r i = 0))) ∧
      ((∃ i, r i ≠ 0) →
        ¬(∀ s : ZMod q, (⟨s, 0⟩ : Q4qCarrier q) ∈
          scalarPeriod40102 p q ζ r u t π))

def centrallySymmetric40121 {α : Type*} [AddGroup α] (A : Set α) : Prop :=
  ∀ x, x ∈ A ↔ -x ∈ A

def translate40121 {α : Type*} [Add α] (A : Set α) (d : α) : Set α :=
  {x | ∃ a, a ∈ A ∧ x = a + d}

/-- Claim 40121: central symmetry of a section and of its target translate
forces a non-saturated nonempty section to have zero translation. -/
def claim40121 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 2 < p →
    ∀ (A : Set (ZMod p)) (d : ZMod p),
      centrallySymmetric40121 A →
      centrallySymmetric40121 (translate40121 A d) →
      ((∀ x, x ∈ A ↔ x + d + d ∈ A) ∧
        (A.Nonempty → A ≠ Set.univ → d = 0))

def additiveCocycle40131 (B M : Type*) [Group B] [AddCommGroup M]
    [DistribMulAction B M] (b : B → M) : Prop :=
  ∀ g h, b (g * h) = b g + g • b h

def voltageConjugacy40131 (B M : Type*) [Group B] [AddCommGroup M]
    [DistribMulAction B M] (b : B → M) (s : M) : Prop :=
  ∀ g x, (g • (x + s) + b g) - s = g • x

/-- Claim 40131: averaging a cocycle over a finite p-prime-to-the-order group
removes all retained additive voltages by one translation. -/
def claim40131 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (B M : Type*) [Fintype B] [Group B]
      [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction B M]
      [SMulCommClass (ZMod p) B M],
    ¬ p ∣ Fintype.card B →
    ∀ b : B → M, additiveCocycle40131 B M b →
      let s : M := (Fintype.card B : ZMod p)⁻¹ • (∑ g : B, b g)
      (∀ g, b g = s - g • s) ∧ voltageConjugacy40131 B M b s

/-- Claim 42723: the two stage-coverage bounds both require at least three
passes for a 26-stage transform. -/
def claim42723 : Prop :=
  Nat.ceil (26 / 11 : ℚ) = 3 ∧
    Nat.ceil (26 / 12 : ℚ) = 3 ∧
    (∀ n : ℕ, 26 ≤ 11 * n → 3 ≤ n) ∧
    (∀ n : ℕ, 26 ≤ 12 * n → 3 ≤ n)

end MathlibPlus.Open.Research.FormalizationBatch
