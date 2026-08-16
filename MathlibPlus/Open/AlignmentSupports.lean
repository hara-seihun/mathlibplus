import Mathlib

namespace MathlibPlus.Open.AlignmentSupports

/-- The centered weight of the `r`th basis vector in degree `k`. -/
def weight (k r : ℕ) : ℤ := (k : ℤ) - 2 * (r : ℤ)

/-- The finite centered weight set `Λₖ`. -/
def Lambda (k : ℕ) : Finset ℤ :=
  (Finset.range (k + 1)).image (weight k)

/-- The diagonal and anti-diagonal alignment supports in `Λₖ²`. -/
def deltaPlus (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (k + 1)).image (fun r => (weight k r, weight k r))

def deltaMinus (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (k + 1)).image (fun r => (weight k r, -weight k r))

/-- The objectwise actions induced by `Jₖ ⊗ I`, `I ⊗ Jₖ`, factor swap, and `w₀`. -/
def R_h (p : ℤ × ℤ) : ℤ × ℤ := (-p.1, p.2)

def R_c (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)

def S (p : ℤ × ℤ) : ℤ × ℤ := (p.2, p.1)

def w0 (p : ℤ × ℤ) : ℤ × ℤ := (-p.1, -p.2)

/-- `R_h` and `R_c` exchange the two alignment supports, while `S` and `w₀`
preserve each support. -/
def weylTransportAlignmentSupports : Prop :=
  ∀ k : ℕ,
    Finset.image R_h (deltaPlus k) = deltaMinus k ∧
    Finset.image R_h (deltaMinus k) = deltaPlus k ∧
    Finset.image R_c (deltaPlus k) = deltaMinus k ∧
    Finset.image R_c (deltaMinus k) = deltaPlus k ∧
    Finset.image S (deltaPlus k) = deltaPlus k ∧
    Finset.image S (deltaMinus k) = deltaMinus k ∧
    Finset.image (w0) (deltaPlus k) = deltaPlus k ∧
    Finset.image (w0) (deltaMinus k) = deltaMinus k

end MathlibPlus.Open.AlignmentSupports
