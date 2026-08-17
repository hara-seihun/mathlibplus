import Mathlib

noncomputable section
open Classical
open scoped BigOperators

namespace MathlibPlus.Open.Fourier.Claim45872

abbrev TernaryVector (e : ℕ) := Fin e → ZMod 3
abbrev TernaryCharacter (e : ℕ) := TernaryVector e →+ ZMod 3

def omega : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

def translateProfile {e : ℕ} (A : Set (TernaryVector e))
    (u : TernaryVector e) : Set (TernaryVector e) :=
  {x | ∃ a ∈ A, x = a + u}

def reflectProfile {e : ℕ} (A : Set (TernaryVector e)) : Set (TernaryVector e) :=
  {x | -x ∈ A}

def profileFourier {e : ℕ} (A : Set (TernaryVector e))
    (χ : TernaryCharacter e) : ℂ :=
  ∑ d : TernaryVector e,
    if d ∈ A then omega ^ (χ d).val else 0

def activePhaseSystem {e : ℕ} (A B : Set (TernaryVector e))
    (u : TernaryVector e) : Prop :=
  ∀ χ : TernaryCharacter e,
    (profileFourier A χ = 0 ∧ profileFourier B χ = 0) ∨
      (profileFourier A χ ≠ 0 ∧
        profileFourier B χ =
          omega ^ (χ u).val * profileFourier A χ)

/-- Translation, reflection, and the one-common-vector criterion for the
complete ternary Fourier tuple.  The active-phase form explicitly records that
zero layers have no phase choice while still requiring the corresponding target
layer to vanish. -/
def claim45872_translation_reflection_common_phase : Prop :=
  (omega ^ 3 = 1 ∧ omega ≠ 1) ∧
  (∀ e : ℕ, 1 ≤ e → e ≤ 2 →
    (∀ (A : Set (TernaryVector e)) (u : TernaryVector e)
        (χ : TernaryCharacter e),
      profileFourier (translateProfile A u) χ =
        omega ^ (χ u).val * profileFourier A χ) ∧
    (∀ (A : Set (TernaryVector e)) (χ : TernaryCharacter e),
      profileFourier (reflectProfile A) χ =
        star (profileFourier A χ)) ∧
    (∀ (A B : Set (TernaryVector e)) (u : TernaryVector e),
      (B = translateProfile A u ↔
        ∀ χ : TernaryCharacter e,
          profileFourier B χ =
            omega ^ (χ u).val * profileFourier A χ) ∧
      (B = translateProfile A u ↔ activePhaseSystem A B u)))

end MathlibPlus.Open.Fourier.Claim45872

end
