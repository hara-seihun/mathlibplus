import Mathlib

namespace MathlibPlus.Open.FrameSkinbookBatch

abbrev FrameHeart (n : ℕ) := Fin n → Fin n → Bool
abbrev FrameInput (n : ℕ) := Fin n → Bool

/-- Boolean parity of a finite set. -/
def parity {α : Type*} [DecidableEq α] (s : Finset α) : Bool :=
  decide (s.card % 2 = 1)

/-- The north output of the finite Boolean frame whose heart is `C`. -/
def frameNorthOutput {n : ℕ} (C : FrameHeart n) (u : FrameInput n) (x : Fin n) : Bool :=
  parity (Finset.univ.filter (fun y => (C y x && u y) = true))

/-- The input with precisely row `y` toggled. -/
def singleRowInput {n : ℕ} (y : Fin n) : FrameInput n :=
  fun z => decide (z = y)

def boolChange (a b : Bool) : Bool := (a && !b) || (!a && b)

def frameRowResponse {n : ℕ} (C : FrameHeart n) (y x : Fin n) : Bool :=
  boolChange (frameNorthOutput C (singleRowInput y) x)
    (frameNorthOutput C (fun _ => false) x)

abbrev Skinbook (n : ℕ) := Finset (Fin n × Fin n × Bool)

def completeSkinbook (C : FrameHeart n) : Skinbook n :=
  (Finset.univ : Finset (Fin n × Fin n)).image
    (fun p => (p.1, p.2, frameRowResponse C p.1 p.2))

def IsCompleteSkinbook (C : FrameHeart n) (S : Skinbook n) : Prop :=
  (∀ y x, ∃! b : Bool, (y, x, b) ∈ S) ∧
    (∀ y x, ∀ b : Bool, (y, x, b) ∈ S → b = frameRowResponse C y x)

noncomputable def skinbookDecode (S : Skinbook n) : FrameHeart n :=
  fun y x => if h : ∃ b : Bool, (y, x, b) ∈ S then Classical.choose h else false

def skinKinEquivalent {n : ℕ} (C C' : FrameHeart n) : Prop :=
  completeSkinbook C = completeSkinbook C'

/-- Claim 9267: the complete table contains one response for every row/output pair. -/
def complete_skinbook_observer_9267 : Prop :=
  ∀ (n : ℕ) (C : FrameHeart n), IsCompleteSkinbook C (completeSkinbook C)

/-- Claim 9268: a single-row Boolean perturbation reads the corresponding heart bit. -/
def single_row_response_identity_9268 : Prop :=
  ∀ (n : ℕ) (C : FrameHeart n) (y x : Fin n),
    frameRowResponse C y x = C y x

/-- Claim 9269: decoding a complete skinbook is a deterministic left inverse. -/
def reconstruction_of_every_heart_entry_9269 : Prop :=
  ∀ (n : ℕ) (C : FrameHeart n),
    IsCompleteSkinbook C (completeSkinbook C) ∧
      skinbookDecode (completeSkinbook C) = C

/-- Claim 9270: complete skinbooks separate finite frame hearts. -/
def injectivity_of_complete_skinbook_9270 : Prop :=
  ∀ (n : ℕ) (C C' : FrameHeart n),
    completeSkinbook C = completeSkinbook C' → C = C'

/-- Claim 9271: equality under the full observer is exactly equality of hearts. -/
def full_skin_kin_equivalence_collapses_to_equality_9271 : Prop :=
  ∀ (n : ℕ) (C C' : FrameHeart n),
    (skinKinEquivalent C C' ↔ C = C')

end MathlibPlus.Open.FrameSkinbookBatch
