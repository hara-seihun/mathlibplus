import Mathlib

namespace MathlibPlus.Open.Research.R1487

abbrev Point (q : ℕ) := ZMod q
abbrev Vector (p q : ℕ) := Point q → ZMod p

/-- The permutation action on the function permutation module. -/
def permute {p q : ℕ} (b : Equiv.Perm (Point q)) (x : Vector p q) : Vector p q :=
  fun y => x (b.symm y)

/-- Explicit two-transitivity for a subgroup of the symmetric group. -/
def IsTwoTransitive {q : ℕ} (B : Subgroup (Equiv.Perm (Point q))) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : Point q,
    x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ b : B, b.1 x₁ = y₁ ∧ b.1 x₂ = y₂

/-- A linear subspace written without hiding its carrier behind a predicate parameter. -/
def IsFpSubspace {p q : ℕ} (U : Set (Vector p q)) : Prop :=
  (0 : Vector p q) ∈ U ∧
    (∀ x y, x ∈ U → y ∈ U → x + y ∈ U) ∧
    (∀ (a : ZMod p) x, x ∈ U → a • x ∈ U)

def IsBInvariant {p q : ℕ} (B : Subgroup (Equiv.Perm (Point q)))
    (U : Set (Vector p q)) : Prop :=
  ∀ b : B, ∀ x, x ∈ U → permute b.1 x ∈ U

def Augmentation {p q : ℕ} [NeZero q] : Set (Vector p q) :=
  {x | ∑ y, x y = 0}

def IsEquivariantEndomorphism {p q : ℕ} (B : Subgroup (Equiv.Perm (Point q)))
    (f : Vector p q → Vector p q) : Prop :=
  (∀ x y, f (x + y) = f x + f y) ∧
    (∀ (a : ZMod p) x, f (a • x) = a • f x) ∧
    (∀ b : B, ∀ x, f (permute b.1 x) = permute b.1 (f x))

/-- Direct-sum complements give the usual finite-dimensional meaning of semisimple. -/
def IsSemisimplePermutationModule {p q : ℕ}
    (B : Subgroup (Equiv.Perm (Point q))) : Prop :=
  ∀ U : Set (Vector p q),
    IsFpSubspace U → IsBInvariant B U →
      ∃ W : Set (Vector p q),
        IsFpSubspace W ∧ IsBInvariant B W ∧
          (∀ u ∈ U, ∀ w ∈ W, u + w = 0 → u = 0 ∧ w = 0) ∧
          (∀ x, ∃ u, u ∈ U ∧ ∃ w, w ∈ W ∧ x = u + w)

def IsSimpleAugmentation {p q : ℕ} [NeZero q]
    (B : Subgroup (Equiv.Perm (Point q))) : Prop :=
  ∀ U : Set (Vector p q),
    IsFpSubspace U → U ⊆ Augmentation → IsBInvariant B U →
      (U = ({0} : Set (Vector p q)) ∨ Augmentation ⊆ U)

def IsScalarOnAugmentation {p q : ℕ} [NeZero q]
    (B : Subgroup (Equiv.Perm (Point q))) : Prop :=
  ∀ f : Vector p q → Vector p q,
    IsEquivariantEndomorphism B f →
    (∀ x, x ∈ Augmentation → f x ∈ Augmentation) →
      ∃ a : ZMod p, ∀ x, x ∈ Augmentation → f x = a • x

/-- Claim 37721: the complete module-theoretic assertion in the packet. -/
def claim_37721 : Prop :=
  ∀ p q : ℕ, Nat.Prime p → (hq : Nat.Prime q) → q < p →
    letI : NeZero q := ⟨Nat.Prime.ne_zero hq⟩
    ∀ B : Subgroup (Equiv.Perm (Point q)), IsTwoTransitive B →
      (¬ p ∣ Nat.card B) ∧
        IsSemisimplePermutationModule (p := p) B ∧
        (∀ (f : Vector p q → Vector p q), IsEquivariantEndomorphism B f →
          ∃ a b : ZMod p, ∀ (x : Vector p q) (y : Point q),
            f x y = a * x y + b * (∑ z, x z)) ∧
        (∀ a b : ZMod p,
          (∀ (x : Vector p q) (y : Point q), a * x y + b * (∑ z, x z) = 0) →
            a = 0 ∧ b = 0) ∧
        IsScalarOnAugmentation (p := p) B ∧ IsSimpleAugmentation (p := p) B

/-- Claim 37737: two distinct coordinate evaluations on the augmentation module. -/
def claim_37737 : Prop :=
  ∀ p q : ℕ, Nat.Prime p → (hq : Nat.Prime q) → q % 2 = 1 →
    letI : NeZero q := ⟨Nat.Prime.ne_zero hq⟩
    ∀ y : Point q, y ≠ 0 →
      (∀ a b : ZMod p,
        (∀ x : Vector p q, x ∈ Augmentation →
          a * x 0 + b * x y = 0) → a = 0 ∧ b = 0) ∧
      (∀ u v : ZMod p,
        ∃ z₃ : Point q, z₃ ≠ 0 ∧ z₃ ≠ y ∧
          ∃ x : Vector p q,
            x ∈ Augmentation ∧ x 0 = u ∧ x y = v ∧
              (∀ z : Point q, z ≠ 0 → z ≠ y → z ≠ z₃ → x z = 0))

abbrev TranslationVector (p n : ℕ) := Fin n → ZMod p

def translationAction {p n : ℕ} {K : Type*} [MulOne K]
    (rho : K →* Equiv.Perm (Fin n))
    (g : K) (x : TranslationVector p n) : TranslationVector p n :=
  fun i => x ((rho g).symm i)

def IsTranslationCocycle {p n : ℕ} {K : Type*} [Group K]
    (rho : K →* Equiv.Perm (Fin n)) (c : K → TranslationVector p n) : Prop :=
  ∀ g h : K, c (g * h) = c g + translationAction rho g (c h)

def averagingCorrection {p n : ℕ} {K : Type*} [Fintype K]
    (c : K → TranslationVector p n) : TranslationVector p n :=
  (-((Fintype.card K : ZMod p)⁻¹)) • (∑ g : K, c g)

def SupportStabilizerOrder (K : Type*) [Fintype K] : Prop :=
  Fintype.card K = 1 ∨ Fintype.card K = 4 ∨ Fintype.card K = 12

/-- Claim 37740: coprime finite support stabilizers have only coboundary discrepancies. -/
def claim_37740 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (K : Type*) [Fintype K] [Group K]
    (n : ℕ) (rho : K →* Equiv.Perm (Fin n))
    (c : K → TranslationVector p n),
    ¬ p ∣ Fintype.card K → IsTranslationCocycle rho c →
      (∀ g : K,
        c g = translationAction rho g (averagingCorrection c) - averagingCorrection c) ∧
      (∃ m : TranslationVector p n, ∀ g : K,
        c g = translationAction rho g m - m) ∧
      (∀ (K' : Type*) [Fintype K'] [Group K']
        (n' : ℕ) (rho' : K' →* Equiv.Perm (Fin n'))
        (c' : K' → TranslationVector p n'),
        p % 2 = 1 → SupportStabilizerOrder K' →
          ¬ p ∣ Fintype.card K' → IsTranslationCocycle rho' c' →
            ∃ m' : TranslationVector p n', ∀ g : K',
              c' g = translationAction rho' g m' - m')

end MathlibPlus.Open.Research.R1487
