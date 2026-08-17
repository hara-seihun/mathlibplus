import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1288

noncomputable section

abbrev Profile (m : ℕ) (X : Type*) := X → ZMod m
abbrev Omega (m : ℕ) (X : Type*) := ZMod m × X

def translationAction {m : ℕ} {X : Type*}
    (v : Profile m X) (p : Omega m X) : Omega m X :=
  (p.1 + v p.2, p.2)

def pointFactor {m : ℕ} {X : Type*}
    (x : X) : Set (Profile m X) :=
  {v | ∀ y : X, y ≠ x → v y = 0}

/-- A permutation conjugates one literal translation profile to another. -/
def conjugatesProfile {m : ℕ} {X : Type*}
    (φ : Equiv.Perm (Omega m X))
    (v w : Profile m X) : Prop :=
  ∀ p : Omega m X,
    φ (translationAction v (φ⁻¹ p)) = translationAction w p

/-- The normalizer predicate for the full independent translation product. -/
def normalizesTranslationProduct {m : ℕ} {X : Type*}
    (φ : Equiv.Perm (Omega m X)) : Prop :=
  ∀ v : Profile m X, ∃ w : Profile m X, conjugatesProfile φ v w

def blockPermutation {m : ℕ} {X : Type*}
    (φ : Equiv.Perm (Omega m X)) (σ : Equiv.Perm X) : Prop :=
  ∀ a : ZMod m, ∀ x : X, (φ (a, x)).2 = σ x

/-- Exact factor transport under a normalizing permutation. -/
def mapsPointFactor {m : ℕ} {X : Type*}
    (φ : Equiv.Perm (Omega m X)) (x y : X) : Prop :=
  (∀ v : Profile m X, v ∈ pointFactor x →
    ∀ w : Profile m X, conjugatesProfile φ v w → w ∈ pointFactor y) ∧
  (∀ w : Profile m X, w ∈ pointFactor y →
    ∃ v : Profile m X, v ∈ pointFactor x ∧ conjugatesProfile φ v w)

/-- Claim 40017: the pointwise-off-block factors are action-determined and
are permuted with the blocks by every normalizer. -/
def claim40017_actionDeterminedFactors : Prop :=
  ∀ m : ℕ, Odd m →
    ∀ (X : Type*) [Fintype X] [DecidableEq X], Fintype.card X = 8 →
      ∀ φ : Equiv.Perm (Omega m X),
        normalizesTranslationProduct φ →
          ∃ σ : Equiv.Perm X,
            blockPermutation φ σ ∧
              ∀ x : X, mapsPointFactor φ x (σ x)

/-- Claim 40018: the full normalizer has the scalar-monomial affine form. -/
def claim40018_fullNormalizerForm : Prop :=
  ∀ m : ℕ, Odd m →
    ∀ (X : Type*) [Fintype X] [DecidableEq X], Fintype.card X = 8 →
      ∀ φ : Equiv.Perm (Omega m X),
        normalizesTranslationProduct φ ↔
          ∃ u : X → (ZMod m)ˣ,
          ∃ t : Profile m X,
          ∃ σ : Equiv.Perm X,
            ∀ a : ZMod m, ∀ x : X,
              φ (a, x) = ((u x : ZMod m) * a + t x, σ x)

end
end MathlibPlus.Open.ResearchFormalization.R1288
