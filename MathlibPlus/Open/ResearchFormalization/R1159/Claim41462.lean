import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1159.Claim41462

noncomputable section

abbrev SThree := Equiv.Perm (Fin 3)
abbrev PrimeFiber (p : ℕ) := ZMod p
abbrev AffineLoop (p : ℕ) := Equiv.Perm (PrimeFiber p)

def primeOneModThree (p : ℕ) : Prop :=
  Nat.Prime p ∧ p % 3 = 1

def denominatorPrime (d : ℕ) : Prop :=
  d = 2 ∨ d = 3 ∨ d = 5

def denominatorUnits (p : ℕ) : Prop :=
  ∀ d : ℕ, denominatorPrime d → IsUnit (d : ZMod p)

def identityFixingNonautomorphic (σ : Equiv.Perm SThree) : Prop :=
  σ 1 = 1 ∧ ∃ a b : SThree, σ (a * b) ≠ σ a * σ b

def normalizedScalarProfile (e : SThree → ZMod 3) : Prop :=
  e 1 = 0

def normalizedTranslationProfile {p : ℕ}
    (τ : SThree → ZMod p) : Prop :=
  τ 1 = 0

def scalarValue {p : ℕ}
    (ω : (ZMod p)ˣ) (e : SThree → ZMod 3) (h : SThree) : ZMod p :=
  (ω : ZMod p) ^ (e h).val

def scalarUnitValue {p : ℕ}
    (ω : (ZMod p)ˣ) (e : SThree → ZMod 3) (h : SThree) : (ZMod p)ˣ :=
  ω ^ (e h).val

def orderThreeMultiplierSubgroup {p : ℕ}
    (ω : (ZMod p)ˣ) : Subgroup (ZMod p)ˣ :=
  Subgroup.closure ({ω, (-1 : (ZMod p)ˣ)} : Set (ZMod p)ˣ)

def thetaIndex (σ : Equiv.Perm SThree) (k h : SThree) : SThree :=
  σ.symm (σ (h * k) * (σ k)⁻¹)

/-- The exact affine map appearing in the normalized relative derivative. -/
def derivativeLoop {p : ℕ}
    (ω : (ZMod p)ˣ) (σ : Equiv.Perm SThree)
    (e : SThree → ZMod 3) (τ : SThree → ZMod p)
    (u : ZMod p) (k h : SThree) (f : AffineLoop p) : Prop :=
  ∀ z : ZMod p,
    f z =
      (scalarValue ω e (thetaIndex σ k h))⁻¹ *
        (scalarValue ω e (h * k) * z +
          (scalarValue ω e (h * k) - scalarValue ω e k) * u +
            τ (h * k) - τ k - τ (thetaIndex σ k h))

/-- Quietness is exactly the vanishing of the scalar-left coefficient in the
relative-derivative formula. -/
def quietDerivativeLoop {p : ℕ}
    (ω : (ZMod p)ˣ) (σ : Equiv.Perm SThree)
    (e : SThree → ZMod 3) (τ : SThree → ZMod p)
    (u : ZMod p) (k h : SThree) (f : AffineLoop p) : Prop :=
  derivativeLoop ω σ e τ u k h f ∧
    scalarValue ω e (h * k) = scalarValue ω e k

/-- A scalar-quiet component is a nonempty family of derivative or inverse
edges, with every derivative edge satisfying the quiet condition. -/
def scalarQuietComponent {p : ℕ}
    (ω : (ZMod p)ˣ) (σ : Equiv.Perm SThree)
    (e : SThree → ZMod 3) (τ : SThree → ZMod p)
    (L : Set (AffineLoop p)) : Prop :=
  L.Nonempty ∧
    ∀ f : AffineLoop p, f ∈ L →
      (∃ u : ZMod p, ∃ k h : SThree,
        quietDerivativeLoop ω σ e τ u k h f) ∨
      (∃ u : ZMod p, ∃ k h : SThree,
        quietDerivativeLoop ω σ e τ u k h f.symm)

def affineLoopForm {p : ℕ}
    (f : AffineLoop p) (a : (ZMod p)ˣ) (b : ZMod p) : Prop :=
  ∀ z : ZMod p, f z = (a : ZMod p) * z + b

def commonCenterEquation {p : ℕ}
    (a : (ZMod p)ˣ) (b c : ZMod p) : Prop :=
  b + ((a : ZMod p) - 1) * c = 0

def affineComponentSaturated {p : ℕ}
    (L : Set (AffineLoop p)) : Prop :=
  ∀ t : ZMod p, ∃ f : AffineLoop p,
    f ∈ (Subgroup.closure L : Set (AffineLoop p)) ∧
      ∀ z : ZMod p, f z = z + t

/-- The common-center and quiet-multiplier identities whose symbolic proof uses
only the displayed denominator primes. -/
def commonCenterMultiplierIdentities {p : ℕ}
    (ω : (ZMod p)ˣ) (σ : Equiv.Perm SThree)
    (e : SThree → ZMod 3) (τ : SThree → ZMod p) : Prop :=
  ∀ L : Set (AffineLoop p),
    scalarQuietComponent ω σ e τ L →
      (∀ f : AffineLoop p, f ∈ L →
        ∃ a : (ZMod p)ˣ, ∃ b : ZMod p,
          affineLoopForm f a b ∧
            a ∈ orderThreeMultiplierSubgroup ω) ∧
      (¬ affineComponentSaturated L →
        ∃ c : ZMod p,
          ∀ f : AffineLoop p, f ∈ L →
            ∃ a : (ZMod p)ˣ, ∃ b : ZMod p,
              affineLoopForm f a b ∧ commonCenterEquation a b c)

/-- Claim 41462: no prime `p ≡ 1 (mod 3)` is exceptional for the exact
order-three affine family: the only symbolic denominators are `2`, `3`, and
`5`, they are units in `𝔽_p`, and the common-center/multiplier identities
specialize throughout the stated profile scope. -/
def claim41462 : Prop :=
  ∀ p : ℕ, primeOneModThree p →
    p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧
      denominatorUnits p ∧
      ∀ (ω : (ZMod p)ˣ), orderOf ω = 3 →
        ∀ (σ : Equiv.Perm SThree), identityFixingNonautomorphic σ →
          ∀ (e : SThree → ZMod 3), normalizedScalarProfile e →
            ∀ (τ : SThree → ZMod p), normalizedTranslationProfile τ →
              commonCenterMultiplierIdentities ω σ e τ

end

end MathlibPlus.Open.ResearchFormalization.R1159.Claim41462
