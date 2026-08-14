import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7

/-- The finite signed word and its state path, with the first entry oriented positive. -/
def firstCentralReturn
    (k h : ℕ) (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ) : Prop :=
  2 ≤ h ∧
  (∀ i : Fin h, ε i = -1 ∨ ε i = 1) ∧
  S ⟨0, Nat.zero_lt_succ h⟩ = 0 ∧
  (∀ i : Fin h,
    S i.succ = 2 * S i.castSucc + (k + i.val + 1 : ℤ) * ε i) ∧
  S (Fin.last h) = 0 ∧
  (∀ i : Fin h, 1 ≤ i.val → S i.castSucc ≠ 0) ∧
  (∀ i : Fin h, 1 ≤ i.val → ε i = -Int.sign (S i.castSucc)) ∧
  (∀ i : Fin h, i.val = 0 → ε i = 1)

/-- A binary block code, with the bound making every requested coordinate valid. -/
def blockCode
    {h : ℕ} (ε : Fin h → ℤ) (start len : ℕ)
    (bound : start + len ≤ h) : ℤ :=
  ∑ i : Fin len,
    ε ⟨start + i.val, by omega⟩ * (2 : ℤ) ^ (len - 1 - i.val)

/-- The first block of a word. -/
def prefixCode {h : ℕ} (ε : Fin h → ℤ) (len : ℕ)
    (bound : len ≤ h) : ℤ :=
  blockCode ε 0 len (by simpa using bound)

/-- The suffix code and its first-moment term at an interior cut. -/
def suffixCode {h : ℕ} (ε : Fin h → ℤ) (s : Fin h) : ℤ :=
  blockCode ε s.val (h - s.val) (by omega)

def suffixMoment {h : ℕ} (ε : Fin h → ℤ) (s : Fin h) : ℤ :=
  ∑ j : Fin (h - s.val),
    (j.val + 1 : ℤ) *
      ε ⟨s.val + j.val, by omega⟩ *
      (2 : ℤ) ^ (h - s.val - 1 - j.val)

def cutState {h : ℕ} (S : Fin (h + 1) → ℤ) (s : Fin h) : ℤ :=
  S s.castSucc

def cutU {h : ℕ} (ε : Fin h → ℤ) (s : Fin h) : ℤ :=
  prefixCode ε s.val (by omega)

def cutV {h : ℕ} (ε : Fin h → ℤ) (s : Fin h) : ℤ :=
  suffixCode ε s

def cutC {h : ℕ} (ε : Fin h → ℤ) (s : Fin h) : ℤ :=
  (2 : ℤ) ^ (h - s.val) * cutU ε s + cutV ε s

def cutQ {h : ℕ} (ε : Fin h → ℤ) (s : Fin h) : ℤ :=
  (2 : ℤ) ^ s.val * cutV ε s + cutU ε s

def wordM (h : ℕ) : ℤ := (2 : ℤ) ^ h - 1

def rotatedResidual
    {h : ℕ} (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ)
    (s : Fin h) : ℤ :=
  -wordM h * cutState S s +
    (h - s.val : ℤ) * cutQ ε s +
    (h : ℤ) * cutU ε s

/-- Exact first-return rotation identities and sign conclusions. -/
def firstReturnCutIdentities : Prop :=
  ∀ (k h : ℕ) (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ),
    firstCentralReturn k h ε S →
    ∀ s : Fin h, 0 < s.val →
      let A := cutState S s
      let U := cutU ε s
      let V := cutV ε s
      let C := cutC ε s
      let Q := cutQ ε s
      let M := wordM h
      let t := h - s.val
      let K : ℤ := (k + h : ℕ)
      let B_V := suffixMoment ε s
      let R := rotatedResidual ε S s
      2 ^ t * A + (K - t) * V + B_V = 0 ∧
      2 ^ t * R = -M * (2 ^ t * A - (t : ℤ) * V) +
        (h + t : ℤ) * C - (h : ℤ) * V ∧
      0 < U ∧
      1 ≤ C ∧ C ≤ (M - 1) / 2 ∧
      Int.sign V = Int.sign Q ∧
      Int.sign Q = -Int.sign A

/-- The sign-opposition conclusion for every proper cyclic rotation. -/
def properRotationOpposition : Prop :=
  ∀ (k h : ℕ) (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ),
    firstCentralReturn k h ε S →
    ∀ s : Fin h, 0 < s.val →
      cutState S s * rotatedResidual ε S s < 0

end MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7
