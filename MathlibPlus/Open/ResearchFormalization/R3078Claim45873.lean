import MathlibPlus.Open.Fourier.Claim45872

noncomputable section
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R3078Claim45873

open MathlibPlus.Open.Fourier.Claim45872

/-- A finite quotient-label set is represented by a finite subset of an
otherwise unrestricted label type. -/
abbrev Label {ι : Type*} (L : Finset ι) := {h // h ∈ L}

def blockwiseMap {e : ℕ} {α : Type*} {L : Finset α}
    (σ : Label L → Label L)
    (t : Label L → TernaryVector e) :
    TernaryVector e × Label L → TernaryVector e × Label L :=
  fun p => (p.1 + t p.2, σ p.2)

def profileSupport {e : ℕ} {α : Type*} {L : Finset α}
    (A : Label L → Set (TernaryVector e)) :
    Set (TernaryVector e × Label L) :=
  {p | p.1 ∈ A p.2}

def profileTransport {e : ℕ} {α : Type*} {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e) : Prop :=
  Set.image (blockwiseMap σ t) (profileSupport A) = profileSupport B

def fibreTransportAt {e : ℕ} {α : Type*} {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e)
    (h : Label L) : Prop :=
  B (σ h) = translateProfile (A h) (t h)

def fibreTransport {e : ℕ} {α : Type*} {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e) : Prop :=
  ∀ h : Label L, fibreTransportAt A B σ t h

def phaseEquationAt {e : ℕ} {α : Type*} {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e)
    (h : Label L) (χ : TernaryCharacter e) : Prop :=
  profileFourier (B (σ h)) χ =
    omega ^ (χ (t h)).val * profileFourier (A h) χ

/-- The displayed phase equation and its zero-layer consequence are kept
 together, so a vanished source layer is never assigned an arbitrary phase. -/
def phaseEquations {e : ℕ} {α : Type*} {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e) : Prop :=
  ∀ h : Label L, ∀ χ : TernaryCharacter e,
    phaseEquationAt A B σ t h χ ∧
      (profileFourier (A h) χ = 0 → profileFourier (B (σ h)) χ = 0)

def inverseLabelSpec {α : Type*} [Neg α] {L : Finset α}
    (ι : Label L → Label L) : Prop :=
  (∀ h : Label L, ι (ι h) = h) ∧
    (∀ h : Label L, (ι h).1 = -h.1)

def inverseCompatibleProfiles {e : ℕ} {α : Type*} [Neg α] {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e)
    (ι : Label L → Label L) : Prop :=
  inverseLabelSpec ι ∧
    (∀ h : Label L, ι (σ h) = σ (ι h)) ∧
    (∀ h : Label L, t (ι h) = -t h) ∧
    (∀ h : Label L, A (ι h) = reflectProfile (A h)) ∧
    (∀ h : Label L,
      B (σ (ι h)) = reflectProfile (B (σ h)))

def inversePhaseEquationAt {e : ℕ} {α : Type*} [Neg α] {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e)
    (ι : Label L → Label L) (h : Label L) (χ : TernaryCharacter e) : Prop :=
  phaseEquationAt A B σ t (ι h) χ

/-- The conjugate of the phase equation at `h`, written at the actual target
fibre and translation belonging to the inverse source label. -/
def conjugatePhaseEquationAt {e : ℕ} {α : Type*} [Neg α] {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e)
    (ι : Label L → Label L) (h : Label L) (χ : TernaryCharacter e) : Prop :=
  profileFourier (B (σ (ι h))) χ =
    star (omega ^ (χ (t h)).val * profileFourier (A h) χ)

/-- The inverse-label equation is paired with the cyclotomic conjugate of the
original equation, with the actual `σ (-h)` and `t (-h)` occurrences retained. -/
def inversePhasePairing {e : ℕ} {α : Type*} [Neg α] {L : Finset α}
    (A B : Label L → Set (TernaryVector e))
    (σ : Label L → Label L) (t : Label L → TernaryVector e)
    (ι : Label L → Label L) : Prop :=
  ∀ h : Label L, ∀ χ : TernaryCharacter e,
    inversePhaseEquationAt A B σ t ι h χ ↔
      conjugatePhaseEquationAt A B σ t ι h χ

/-- Claim 45873: blockwise image transport, fibre-set transport, all Fourier
phase equations including zero layers, and the inverse-label conjugation
pairing. -/
def claim45873 : Prop :=
  ∀ (e : ℕ), (e = 1 ∨ e = 2) →
    ∀ (α : Type*) [DecidableEq α] [Neg α] (L : Finset α)
      (A B : Label L → Set (TernaryVector e))
      (σ : Label L → Label L) (t : Label L → TernaryVector e),
      Function.Bijective σ →
      (profileTransport A B σ t ↔ fibreTransport A B σ t) ∧
        (fibreTransport A B σ t ↔ phaseEquations A B σ t) ∧
        (phaseEquations A B σ t →
          ∀ h : Label L, ∀ χ : TernaryCharacter e,
            profileFourier (A h) χ = 0 →
              profileFourier (B (σ h)) χ = 0) ∧
        (∀ ι : Label L → Label L,
          inverseCompatibleProfiles A B σ t ι →
            inversePhasePairing A B σ t ι)

end MathlibPlus.Open.ResearchFormalization.R3078Claim45873
