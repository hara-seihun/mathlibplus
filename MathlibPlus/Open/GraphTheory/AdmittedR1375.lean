import Mathlib

noncomputable section

namespace MathlibPlus.Open.GraphTheory.R1375

def inTwoClosure {α : Type*}
    (G : Subgroup (Equiv.Perm α)) (q : Equiv.Perm α) : Prop :=
  ∀ x y : α, ∃ g : G,
    (g : Equiv.Perm α) x = q x ∧ (g : Equiv.Perm α) y = q y

def pureLift {Δ B : Type*}
    (q : Equiv.Perm B) : Equiv.Perm (Δ × B) :=
  Equiv.prodCongr (Equiv.refl Δ) q

def claim38367 : Prop :=
  ∀ {Δ B : Type*} [Fintype Δ] [Fintype B]
    (X : Subgroup (Equiv.Perm B))
    (A : Subgroup (Equiv.Perm (Δ × B))),
    (∀ x : X, pureLift x.1 ∈ A) →
    ∀ q : Equiv.Perm B,
      inTwoClosure X q → inTwoClosure A (pureLift q)

def claim38368 : Prop :=
  ∀ {Δ B : Type*} [Fintype Δ] [Fintype B]
    (X : Subgroup (Equiv.Perm B))
    (A : Subgroup (Equiv.Perm (Δ × B)))
    (q : Equiv.Perm B),
    (∀ x : X, pureLift x.1 ∈ A) →
    inTwoClosure X q →
    inTwoClosure A (pureLift q)

def evaluationKernel {p : ℕ} {B : Type*} [Fact p.Prime]
    (K : Submodule (ZMod p) (B → ZMod p)) (b₀ : B) : Set (B → ZMod p) :=
  {k | k ∈ K ∧ k b₀ = 0}

def commonZeroSet {p : ℕ} {B : Type*} [Fact p.Prime]
    (K : Submodule (ZMod p) (B → ZMod p)) (b₀ : B) : Set B :=
  {b | ∀ k : B → ZMod p, k ∈ evaluationKernel K b₀ → k b = 0}

def precomposePermutation {p : ℕ} {B : Type*} [Fact p.Prime]
    (k : B → ZMod p) (x : Equiv.Perm B) : B → ZMod p :=
  fun b => k (x.symm b)

def claim38369 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (B : Type*) [Fintype B] (X : Subgroup (Equiv.Perm B))
    (K : Submodule (ZMod p) (B → ZMod p)) (b₀ : B),
    (∀ x : X, ∀ k : B → ZMod p, k ∈ K → precomposePermutation k x.1 ∈ K) →
    (∀ x : X, x.1 b₀ = b₀ →
      ∀ k : B → ZMod p,
        k ∈ evaluationKernel K b₀ →
        precomposePermutation k x.1 ∈ evaluationKernel K b₀) ∧
    (∀ x : X, x.1 b₀ = b₀ →
      ∀ b : B, b ∈ commonZeroSet K b₀ → x.1 b ∈ commonZeroSet K b₀)

def fiberTranslation {p : ℕ} {B : Type*} [Fact p.Prime]
    (k : B → ZMod p) : Equiv.Perm (ZMod p × B) :=
  { toFun := fun z => (z.1 + k z.2, z.2)
    invFun := fun z => (z.1 - k z.2, z.2)
    left_inv := by
      intro z
      cases z with
      | mk x b => simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    right_inv := by
      intro z
      cases z with
      | mk x b => simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }

def basePermutation {p : ℕ} {B : Type*} [Fact p.Prime]
    (x : Equiv.Perm B) : Equiv.Perm (ZMod p × B) :=
  Equiv.prodCongr (Equiv.refl (ZMod p)) x

def pointStabilizerOrbit {p : ℕ} {B : Type*} [Fact p.Prime]
    (A : Subgroup (Equiv.Perm (ZMod p × B)))
    (b₀ : B) (z w : ZMod p × B) : Prop :=
  ∃ a : A, a.1 (0, b₀) = (0, b₀) ∧ a.1 z = w

def isPointStabilizerOrbit {B : Type*}
    (X : Subgroup (Equiv.Perm B)) (b₀ : B) (O : Set B) : Prop :=
  O.Nonempty ∧
    (∀ b : B, b ∈ O → ∀ c : B, c ∈ O →
      ∃ x : X, x.1 b₀ = b₀ ∧ x.1 b = c)

def claim38370 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (B : Type*) [Fintype B]
    (X : Subgroup (Equiv.Perm B))
    (K : Submodule (ZMod p) (B → ZMod p)) (b₀ : B)
    (O : Set B),
    (∀ x : X, ∀ k : B → ZMod p, k ∈ K → precomposePermutation k x.1 ∈ K) →
    isPointStabilizerOrbit X b₀ O →
    let A : Subgroup (Equiv.Perm (ZMod p × B)) :=
      Subgroup.closure
        ((fiberTranslation '' (K : Set (B → ZMod p))) ∪
          (basePermutation '' (X : Set (Equiv.Perm B))))
    let Z := commonZeroSet K b₀
    ((O ⊆ Z →
        ∀ (z z' : ZMod p) (b c : B), b ∈ O → c ∈ O →
          (pointStabilizerOrbit A b₀ (z, b) (z', c) ↔ z = z')) ∧
      (¬ O ⊆ Z →
        ∀ (z z' : ZMod p) (b c : B), b ∈ O → c ∈ O →
          pointStabilizerOrbit A b₀ (z, b) (z', c)))

def permutationRegular {α : Type*} [Fintype α]
    (G : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! g : G, (g : Equiv.Perm α) x = y

def claim38371 : Prop :=
  ∀ {α : Type*} [Fintype α]
    (G : Subgroup (Equiv.Perm α)),
    permutationRegular G →
    ∀ q : Equiv.Perm α, inTwoClosure G q → q ∈ G

end MathlibPlus.Open.GraphTheory.R1375
