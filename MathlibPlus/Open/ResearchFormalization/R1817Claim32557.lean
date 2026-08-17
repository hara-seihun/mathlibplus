import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1817

noncomputable section

open scoped BigOperators

abbrev claim32557_Field (p : ℕ) := ZMod p
abbrev claim32557_Functions (p : ℕ) := claim32557_Field p → claim32557_Field p

def claim32557_shift (p : ℕ) (a : claim32557_Field p)
    (h : claim32557_Functions p) : claim32557_Functions p :=
  fun x => h (x + a)

def claim32557_difference (p : ℕ) (h : claim32557_Functions p) : claim32557_Functions p :=
  claim32557_shift p 1 h - h

def claim32557_shiftLinear (p : ℕ) (a : claim32557_Field p) :
    claim32557_Functions p →ₗ[claim32557_Field p] claim32557_Functions p :=
  LinearMap.pi (fun x : claim32557_Field p =>
    LinearMap.proj (R := claim32557_Field p)
      (φ := fun _ : claim32557_Field p => claim32557_Field p) (x + a))

def claim32557_differenceLinear (p : ℕ) :
    claim32557_Functions p →ₗ[claim32557_Field p] claim32557_Functions p :=
  claim32557_shiftLinear p 1 - LinearMap.id

def claim32557_leastPositiveExponent (p : ℕ)
    (f : claim32557_Functions p) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ((claim32557_differenceLinear p) ^ n) f = 0}

def claim32557_depth (p : ℕ) (f : claim32557_Functions p) : ℕ :=
  @ite ℕ (f = 0) (Classical.propDecidable (f = 0))
    1 (claim32557_leastPositiveExponent p f - 1)

def claim_32557 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 2 = 1 →
    (∀ h : claim32557_Functions p,
      ((claim32557_differenceLinear p) ^ p) h = 0) ∧
      (∀ h x, claim32557_differenceLinear p h x = h (x + 1) - h x) ∧
      (∀ f : claim32557_Functions p, f ≠ 0 →
        let s := claim32557_leastPositiveExponent p f
        0 < s ∧
          ((claim32557_differenceLinear p) ^ s) f = 0 ∧
          (∀ n : ℕ, 0 < n →
            ((claim32557_differenceLinear p) ^ n) f = 0 → s ≤ n) ∧
          claim32557_depth p f = s - 1) ∧
      claim32557_depth p 0 = 1

end

end MathlibPlus.Open.ResearchFormalization.R1817
