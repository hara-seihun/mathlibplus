import Mathlib

namespace MathlibPlus.Open.Research.R1159

abbrev SThree := Equiv.Perm (Fin 3)

/-- The prime and congruence assumptions in the resonant family. -/
def PrimeOneModThree (p : ℕ) : Prop := Nat.Prime p ∧ p % 3 = 1

def OrderThree {p : ℕ} (ω : (ZMod p)ˣ) : Prop := orderOf ω = 3

def IdentityFixingNonautomorphic (σ : Equiv.Perm SThree) : Prop :=
  σ 1 = 1 ∧ ∃ a b : SThree, σ (a * b) ≠ σ a * σ b

def NormalizedScalarProfile (e : SThree → ZMod 3) : Prop := e 1 = 0

def NormalizedTranslationProfile {p : ℕ} (τ : SThree → ZMod p) : Prop := τ 1 = 0

def ScalarValue {p : ℕ} (ω : (ZMod p)ˣ) (e : SThree → ZMod 3) (h : SThree) : ZMod p :=
  (ω : ZMod p) ^ (e h).val

def claim31689 : Prop :=
  ∀ (p : ℕ), PrimeOneModThree p →
    ∀ (ω : (ZMod p)ˣ), OrderThree ω →
      ∀ (σ : Equiv.Perm SThree), IdentityFixingNonautomorphic σ →
        ∀ (e : SThree → ZMod 3), NormalizedScalarProfile e →
          ∀ (τ : SThree → ZMod p), NormalizedTranslationProfile τ →
            ∃! f : (ZMod p × SThree) → (ZMod p × SThree),
              ∀ (z : ZMod p) (h : SThree),
                f (z, h) =
                  (ScalarValue ω e h * z + τ h, σ h)

def claim41453 : Prop :=
  ∀ (p : ℕ), PrimeOneModThree p →
    ∀ (ω : (ZMod p)ˣ), OrderThree ω →
      ∀ (σ : Equiv.Perm SThree), IdentityFixingNonautomorphic σ →
        ∀ (e : SThree → ZMod 3), NormalizedScalarProfile e →
          ∀ (τ : SThree → ZMod p), NormalizedTranslationProfile τ →
            ∃! f : (ZMod p × SThree) → (ZMod p × SThree),
              ∀ (z : ZMod p) (h : SThree),
                f (z, h) =
                  (ScalarValue ω e h * z + τ h, σ h)

def claim31692 : Prop :=
  ∀ (p : ℕ), PrimeOneModThree p →
    ∀ (ω : (ZMod p)ˣ), OrderThree ω →
      ∀ (σ : Equiv.Perm SThree), IdentityFixingNonautomorphic σ →
        ∀ (e : SThree → ZMod 3), NormalizedScalarProfile e →
          ∀ (τ : SThree → ZMod p), NormalizedTranslationProfile τ →
            ∃! D : (ZMod p × SThree) → (ZMod p × SThree) → (ZMod p × SThree),
              ∀ (u : ZMod p) (k h : SThree) (z : ZMod p),
                D (u, k) (z, h) =
                  ( (ScalarValue ω e (σ.symm (σ (h * k) * (σ k)⁻¹)))⁻¹ *
                      (ScalarValue ω e (h * k) * z +
                        (ScalarValue ω e (h * k) - ScalarValue ω e k) * u +
                        τ (h * k) - τ k -
                        τ (σ.symm (σ (h * k) * (σ k)⁻¹))),
                    σ.symm (σ (h * k) * (σ k)⁻¹) )

def claim41456 : Prop :=
  ∀ (p : ℕ), PrimeOneModThree p →
    ∀ (ω : (ZMod p)ˣ), OrderThree ω →
      ∀ (σ : Equiv.Perm SThree), IdentityFixingNonautomorphic σ →
        ∀ (e : SThree → ZMod 3), NormalizedScalarProfile e →
          ∀ (τ : SThree → ZMod p), NormalizedTranslationProfile τ →
            ∃! D : (ZMod p × SThree) → (ZMod p × SThree) → (ZMod p × SThree),
              ∀ (u : ZMod p) (k h : SThree) (z : ZMod p),
                D (u, k) (z, h) =
                  ( (ScalarValue ω e (σ.symm (σ (h * k) * (σ k)⁻¹)))⁻¹ *
                      (ScalarValue ω e (h * k) * z +
                        (ScalarValue ω e (h * k) - ScalarValue ω e k) * u +
                        τ (h * k) - τ k -
                        τ (σ.symm (σ (h * k) * (σ k)⁻¹))),
                    σ.symm (σ (h * k) * (σ k)⁻¹) )

end MathlibPlus.Open.Research.R1159
