import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.NevilleGamma

noncomputable section

/-- A positive lower-triangular array of Neville multipliers. -/
structure PositiveNevilleTriangle14809 where
  multiplier : ℕ → ℕ → ℝ
  positive : ∀ {r c : ℕ}, c < r → 0 < multiplier r c

/-- The multiplier entry m_(r,c) of a positive Neville triangle. -/
def nevilleMultiplier14809 (T : PositiveNevilleTriangle14809) (r c : ℕ) : ℝ :=
  T.multiplier r c

/-- The vertical ratio r_c = m_(c+2,c) / m_(c+1,c). -/
def nevilleVerticalRatio14809 (T : PositiveNevilleTriangle14809) (c : ℕ) : ℝ :=
  nevilleMultiplier14809 T (c + 2) c /
    nevilleMultiplier14809 T (c + 1) c

/-- The product R_h = ∏_(c<h) r_c. -/
def nevilleCumulativeRatio14809 (T : PositiveNevilleTriangle14809) (h : ℕ) : ℝ :=
  Finset.prod (Finset.range h) (fun c => nevilleVerticalRatio14809 T c)

/-- The singleton activity w_h = R_h / a_h, with a_h=m_(h+1,h). -/
def nevilleSingletonActivity14809
    (T : PositiveNevilleTriangle14809) (h : ℕ) : ℝ :=
  nevilleCumulativeRatio14809 T h /
    nevilleMultiplier14809 T (h + 1) h

/-- The exact Neville-hole weight for a finite hole set in degree n. -/
def nevilleHoleWeight14809
    (T : PositiveNevilleTriangle14809) (n : ℕ) (H : Finset ℕ) : ℝ :=
  Finset.prod (Finset.range n) (fun c =>
    if c ∈ H then
      (nevilleMultiplier14809 T (c + 1) c)⁻¹
    else
      nevilleMultiplier14809 T
          (c + 1 + (H.filter (fun h => c < h)).card) c /
        nevilleMultiplier14809 T (c + 1) c)

/-- The normalized hole interaction I(H)=W(H)/∏_(h∈H)w_h. -/
def nevilleInteraction14809
    (T : PositiveNevilleTriangle14809) (n : ℕ) (H : Finset ℕ) : ℝ :=
  nevilleHoleWeight14809 T n H /
    Finset.prod H (fun h => nevilleSingletonActivity14809 T h)

/-- The hole universe H_*={0,...,n-1}. -/
def nevilleHoleUniverse14809 (n : ℕ) : Finset ℕ :=
  Finset.range n

/-- Claim 14809: in every positive Neville triangle, the normalized
all-hole interaction is the product of inverse vertical ratios, with the
exact exponent range c=0,...,n-2. -/
def claim14809 : Prop :=
  ∀ (T : PositiveNevilleTriangle14809) (n : ℕ),
    1 ≤ n →
      nevilleInteraction14809 T n (nevilleHoleUniverse14809 n) =
        Finset.prod (Finset.range (n - 1)) (fun c =>
          (nevilleVerticalRatio14809 T c)⁻¹ ^ (n - 1 - c))

end

end MathlibPlus.Open.Combinatorics.NevilleGamma
